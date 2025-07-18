package hashstruct

import (
	"encoding/binary"
	"fmt"
	"hash"
	"io"
	"reflect"
	"strings"
	"time"
)

// Hash returns the hash value of an arbitrary value.
//
// Options can be provided to customize the hashing behavior using the functional
// options pattern. Available options include WithHasher, WithTagName, WithZeroNil,
// WithIgnoreZeroValue, WithSlicesAsSets, and WithUseStringer. If no options
// are provided, default values will be used. The same Option functions can
// be used concurrently.
//
// Notes on the value:
//
//   - Unexported fields on structs are ignored and do not affect the
//     hash value.
//
//   - Adding an exported field to a struct with the zero value will change
//     the hash value.
//
// For structs, the hashing can be controlled using tags. For example:
//
//	struct {
//	    Name     string
//	    UUID     string     `hash:"ignore"`
//	    Tags     []string   `hash:"set"`
//	    Created  time.Time  `hash:"string"`
//	    Updated  time.Time  `hash:"utc"`
//	    Field1   int        `hash:"name=FieldOne"`
//	    Field2   int        `hash:"FieldTwo"`
//	    Date     time.Time  `hash:"eventDate,utc"`
//	}
//
// The available tag values are:
//
//   - "ignore" or "-" - The field will be ignored and not affect the hash code.
//
//   - "set" - The field will be treated as a set, where ordering doesn't
//     affect the hash code. This only works for slices. For example,
//     []string{"a", "b"} and []string{"b", "a"} will produce the same hash.
//
//   - "string" - The field will be hashed as a string using its String() method.
//     This only works when the field implements fmt.Stringer. This is particularly
//     useful for types like time.Time.
//
//   - "utc" - The field will be converted to UTC before hashing. This only works
//     for time.Time fields. This is useful when you want times in different
//     timezones that represent the same moment to produce the same hash.
//
//   - "name=<fieldname>" or just "<fieldname>" - Override the field name used in the hash.
//     This allows you to rename struct fields without changing the hash value.
//     For example, `hash:"name=Field1"` or `hash:"Field1"` will use "Field1" as the
//     field name in the hash regardless of the actual Go field name. This is useful
//     for protecting against field renaming during refactoring. Multiple fields cannot
//     use the same hash field name - this will cause an error.
//
// Tags can be combined with commas, for example: `hash:"name=eventDate,utc"`.
func Hash(v any, options ...Option) ([]byte, error) {
	// Create default config
	cfg := defaultConfig()

	// Apply all options
	for _, opt := range options {
		opt(cfg)
	}

	// Reset the hash
	cfg.hasher.Reset()

	// Fast path for strings.
	if s, ok := v.(string); ok {
		return hashString(cfg.hasher, s)
	}

	// Create our walker and walk the structure
	w := &walker{
		h:               cfg.hasher,
		tag:             cfg.tagName,
		zeronil:         cfg.zeroNil,
		ignorezerovalue: cfg.ignoreZeroValue,
		sets:            cfg.slicesAsSets,
		stringer:        cfg.useStringer,
	}
	return w.visit(reflect.ValueOf(v), nil)
}

type walker struct {
	h               hash.Hash
	tag             string
	zeronil         bool
	ignorezerovalue bool
	sets            bool
	stringer        bool
}

type visitOpts struct {
	// Flags are a bitmask of flags to affect behavior of this visit
	Flags visitFlag

	// Information about the struct containing this field
	Struct      any
	StructField string
}

const (
	// Tag values.
	tagIgnore = "ignore"
	tagString = "string"
	tagSet    = "set"
	tagDash   = "-"
	tagUTC    = "utc"
	tagName   = "name"
)

var timeType = reflect.TypeOf(time.Time{}) //nolint:gochecknoglobals // ok

// parsedTagInfo holds the parsed tag information.
type parsedTagInfo struct {
	name   string
	ignore bool
	set    bool
	utc    bool
	string bool
}

// isKnownTag checks if a tag part is a known tag without allocations.
func isKnownTag(part string) bool {
	switch part {
	case tagIgnore, tagString, tagSet, tagDash, tagUTC:
		return true
	default:
		return false
	}
}

// parseSingleTag handles a single tag part and updates the result.
func parseSingleTag(part string, result *parsedTagInfo) {
	// Check for name=value syntax
	if strings.HasPrefix(part, "name=") {
		result.name = part[5:]
		return
	}

	// Handle known tags
	switch part {
	case tagIgnore, tagDash:
		result.ignore = true
	case tagSet:
		result.set = true
	case tagUTC:
		result.utc = true
	case tagString:
		result.string = true
	default:
		// If it's not a known tag and we don't have a name yet, treat as shorthand name
		if !isKnownTag(part) && result.name == "" {
			result.name = part
		}
	}
}

// parseMultipleTags handles comma-separated tag values.
func parseMultipleTags(tag string) parsedTagInfo {
	result := parsedTagInfo{} //nolint:exhaustruct // zero values are intended
	start := 0

	for i := 0; i <= len(tag); i++ {
		if i == len(tag) || tag[i] == ',' {
			if i > start {
				part := strings.TrimSpace(tag[start:i])
				if part != "" {
					parseSingleTag(part, &result)
				}
			}
			start = i + 1
		}
	}

	return result
}

// parseTag parses a struct tag value and returns the parsed information.
func parseTag(tag string) parsedTagInfo {
	if tag == "" {
		return parsedTagInfo{} //nolint:exhaustruct // zero values are intended
	}

	// Handle shorthand ignore cases
	if tag == tagIgnore || tag == tagDash {
		return parsedTagInfo{ignore: true} //nolint:exhaustruct // only ignore field needed
	}

	// Fast path for single values
	if !strings.Contains(tag, ",") {
		result := parsedTagInfo{} //nolint:exhaustruct // zero values are intended
		parseSingleTag(tag, &result)
		return result
	}

	// Multiple values - parse comma-separated
	return parseMultipleTags(tag)
}

// A direct hash calculation used for numeric and bool values.
func (w *walker) hashDirect(v any) ([]byte, error) {
	w.h.Reset()
	err := binary.Write(w.h, binary.LittleEndian, v)
	return w.h.Sum(nil), err
}

// A direct hash calculation used for strings.
func (w *walker) hashString(s string) ([]byte, error) {
	return hashString(w.h, s)
}

// A direct hash calculation used for strings.
func hashString(h hash.Hash, s string) ([]byte, error) {
	h.Reset()
	_, err := io.WriteString(h, s)
	return h.Sum(nil), err
}

func (w *walker) visit(v reflect.Value, opts *visitOpts) ([]byte, error) {
	t := reflect.TypeOf(0)

	// Loop since these can be wrapped in multiple layers of pointers
	// and interfaces.
	for {
		// If we have an interface, dereference it. We have to do this up
		// here because it might be a nil in there and the check below must
		// catch that.
		if v.Kind() == reflect.Interface {
			v = v.Elem()
			continue
		}

		if v.Kind() == reflect.Ptr {
			if w.zeronil {
				t = v.Type().Elem()
			}
			v = reflect.Indirect(v)
			continue
		}

		break
	}

	// If it is nil, treat it like a zero.
	if !v.IsValid() {
		v = reflect.Zero(t)
	}

	if v.CanInt() {
		if v.Kind() == reflect.Int {
			// binary.Write requires a fixed-size value.
			return w.hashDirect(v.Int())
		}
		return w.hashDirect(v.Interface())
	}

	if v.CanUint() {
		if v.Kind() == reflect.Uint {
			// binary.Write requires a fixed-size value.
			return w.hashDirect(v.Uint())
		}
		return w.hashDirect(v.Interface())
	}

	if v.CanFloat() || v.CanComplex() {
		return w.hashDirect(v.Interface())
	}

	k := v.Kind()

	if k == reflect.Bool {
		var tmp int8
		if v.Bool() {
			tmp = 1
		}
		return w.hashDirect(tmp)
	}

	if v.Type() == timeType {
		w.h.Reset()
		timeVal, ok := v.Interface().(time.Time)
		if !ok {
			return nil, fmt.Errorf("expected time.Time but got %T", v.Interface())
		}
		b, err := timeVal.MarshalBinary()
		if err != nil {
			return nil, err
		}

		if err = binary.Write(w.h, binary.LittleEndian, b); err != nil {
			return nil, err
		}
		return w.h.Sum(nil), nil
	}

	switch k {
	case reflect.Bool, reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
		reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr,
		reflect.Float32, reflect.Float64, reflect.Complex64, reflect.Complex128:
		// These types are handled above before reaching this switch
		return nil, fmt.Errorf("unexpected type %s reached switch statement", k)
	case reflect.Array:
		return w.visitArray(v)

	case reflect.Map:
		return w.visitMap(v, opts)

	case reflect.Struct:
		return w.visitStruct(v, opts)

	case reflect.Slice:
		return w.visitSlice(v, opts)

	case reflect.String:
		return w.hashString(v.String())
	case reflect.Invalid:
		// Invalid values are treated as nil/zero
		return w.hashDirect(int8(0))
	case reflect.Chan, reflect.Func, reflect.UnsafePointer:
		// These types cannot be hashed meaningfully
		return nil, fmt.Errorf("cannot hash type %s", k)
	case reflect.Interface:
		// Interfaces should have been dereferenced earlier
		return nil, fmt.Errorf("unexpected interface type: %s", k)
	case reflect.Ptr:
		// Pointers should have been dereferenced earlier
		return nil, fmt.Errorf("unexpected pointer type: %s", k)
	default:
		return nil, fmt.Errorf("unknown kind to hash: %s", k)
	}
}

func (w *walker) visitMap(v reflect.Value, opts *visitOpts) ([]byte, error) {
	var includeMap IncludableMap
	var field string

	if impl, ok := v.Interface().(IncludableMap); ok {
		includeMap = impl
	} else if opts != nil && opts.Struct != nil {
		if structImpl, structOk := opts.Struct.(IncludableMap); structOk {
			includeMap, field = structImpl, opts.StructField
		}
	}

	// Build the hash for the map. We do this by XOR-ing all the key
	// and value hashes. This makes it deterministic despite ordering.
	h := make([]byte, w.h.Size())

	k := reflect.New(v.Type().Key()).Elem()
	vv := reflect.New(v.Type().Elem()).Elem()

	iter := v.MapRange()

	for iter.Next() {
		k.SetIterKey(iter)
		vv.SetIterValue(iter)
		if includeMap != nil {
			incl, err := includeMap.HashIncludeMap(field, k.Interface(), vv.Interface())
			if err != nil {
				return nil, err
			}
			if !incl {
				continue
			}
		}

		kh, err := w.visit(k, nil)
		if err != nil {
			return nil, err
		}
		vh, err := w.visit(vv, nil)
		if err != nil {
			return nil, err
		}

		fieldHash := hashUpdateOrdered(w.h, kh, vh)
		h = hashUpdateUnordered(h, fieldHash)
	}

	// Important: read the docs for hashFinishUnordered
	h = hashFinishUnordered(w.h, h)

	return h, nil
}

func (w *walker) visitArray(v reflect.Value) ([]byte, error) {
	h := make([]byte, w.h.Size())
	l := v.Len()
	for i := range l {
		current, err := w.visit(v.Index(i), nil)
		if err != nil {
			return nil, err
		}

		h = hashUpdateOrdered(w.h, h, current)
	}

	return h, nil
}

func (w *walker) visitSlice(v reflect.Value, opts *visitOpts) ([]byte, error) {
	// We have two behaviors here. If it isn't a set, then we just
	// visit all the elements. If it is a set, then we do a deterministic
	// hash code.
	var set bool
	if opts != nil {
		set = (opts.Flags & visitFlagSet) != 0
	}

	if set || w.sets {
		// For sets, we need to deduplicate elements to avoid XOR cancellation
		// with duplicate items. We collect unique hashes and sort them for
		// deterministic ordering.
		uniqueHashes := make(map[string][]byte)

		for i := range v.Len() {
			current, err := w.visit(v.Index(i), nil)
			if err != nil {
				return nil, err
			}

			// Use the hash as a key to deduplicate
			key := string(current)
			uniqueHashes[key] = current
		}

		// Sort the unique hashes for deterministic ordering
		sortedHashes := make([][]byte, 0, len(uniqueHashes))
		for _, hashBytes := range uniqueHashes {
			sortedHashes = append(sortedHashes, hashBytes)
		}

		// Sort by comparing byte slices
		for i := range len(sortedHashes) - 1 {
			for j := i + 1; j < len(sortedHashes); j++ {
				if compareBytes(sortedHashes[i], sortedHashes[j]) > 0 {
					sortedHashes[i], sortedHashes[j] = sortedHashes[j], sortedHashes[i]
				}
			}
		}

		// Combine the sorted unique hashes
		h := make([]byte, w.h.Size())
		for _, hashBytes := range sortedHashes {
			h = hashUpdateOrdered(w.h, h, hashBytes)
		}

		return h, nil
	}

	// For non-sets, preserve original ordered behavior
	h := make([]byte, w.h.Size())
	for i := range v.Len() {
		current, err := w.visit(v.Index(i), nil)
		if err != nil {
			return nil, err
		}
		h = hashUpdateOrdered(w.h, h, current)
	}

	return h, nil
}

func (w *walker) processStructField( //nolint:revive // ok in this case
	v reflect.Value, i int, structType reflect.Type, include Includable, parent any,
) (fieldHash []byte, shouldInclude bool, fieldName string, err error) {
	innerV := v.Field(i)
	fieldType := structType.Field(i)

	if fieldType.PkgPath != "" {
		// Unexported field
		return nil, false, "", nil
	}

	tag := fieldType.Tag.Get(w.tag)
	parsedTag := parseTag(tag)

	if parsedTag.ignore {
		// Ignore this field
		return nil, false, "", nil
	}

	if w.ignorezerovalue && innerV.IsZero() {
		return nil, false, "", nil
	}

	// Determine the field name to use for hashing
	if parsedTag.name != "" {
		fieldName = parsedTag.name
	} else {
		fieldName = fieldType.Name
	}

	// if utc is set, convert time.Time to UTC
	if parsedTag.utc {
		if innerV.Type() != timeType {
			// We only show this error if the tag explicitly
			// requests UTC conversion.
			return nil, false, "", &NotTimeError{
				Field: v.Type().Field(i).Name,
			}
		}
		timeVal, ok := innerV.Interface().(time.Time)
		if !ok {
			return nil, false, "", fmt.Errorf("expected time.Time but got %T", innerV.Interface())
		}
		// Convert to UTC and replace the value
		innerV = reflect.ValueOf(timeVal.UTC())
	}

	// if string is set, use the string value
	if parsedTag.string || w.stringer {
		if impl, ok := innerV.Interface().(fmt.Stringer); ok {
			innerV = reflect.ValueOf(impl.String())
		} else if parsedTag.string {
			// We only show this error if the tag explicitly
			// requests a stringer.
			return nil, false, "", &NotStringerError{
				Field: v.Type().Field(i).Name,
			}
		}
	}

	// Check if we implement includable and check it
	if include != nil {
		incl, includeErr := include.HashInclude(fieldType.Name, innerV)
		if includeErr != nil {
			return nil, false, "", includeErr
		}
		if !incl {
			return nil, false, "", nil
		}
	}

	var f visitFlag
	if parsedTag.set {
		f |= visitFlagSet
	}

	kh, keyErr := w.visit(reflect.ValueOf(fieldName), nil)
	if keyErr != nil {
		return nil, false, "", keyErr
	}

	vh, valueErr := w.visit(innerV, &visitOpts{
		Flags:       f,
		Struct:      parent,
		StructField: fieldType.Name,
	})
	if valueErr != nil {
		return nil, false, "", valueErr
	}

	fieldHash = hashUpdateOrdered(w.h, kh, vh)
	return fieldHash, true, fieldName, nil
}

func (w *walker) visitStruct(v reflect.Value, _ *visitOpts) ([]byte, error) {
	parent := v.Interface()
	var include Includable
	if impl, ok := parent.(Includable); ok {
		include = impl
	}

	if impl, ok := parent.(Hashable); ok {
		return impl.Hash()
	}

	// If we can address this value, check if the pointer value
	// implements our interfaces and use that if so.
	if v.CanAddr() {
		vptr := v.Addr()
		parentptr := vptr.Interface()
		if impl, ok := parentptr.(Includable); ok {
			include = impl
		}

		if impl, ok := parentptr.(Hashable); ok {
			return impl.Hash()
		}
	}

	structType := v.Type()
	h, err := w.visit(reflect.ValueOf(structType.Name()), nil)
	if err != nil {
		return nil, err
	}

	// Track field names to detect duplicates
	usedNames := make(map[string]string)

	l := v.NumField()
	for i := range l {
		if v.CanSet() || structType.Field(i).Name != "_" {
			fieldHash, shouldInclude, fieldName, fieldErr := w.processStructField(v, i, structType, include, parent)
			if fieldErr != nil {
				return nil, fieldErr
			}
			if shouldInclude {
				// Check for duplicate field names
				if existingField, exists := usedNames[fieldName]; exists {
					return nil, fmt.Errorf("duplicate hash field name '%s' found in fields '%s' and '%s'",
						fieldName, existingField, structType.Field(i).Name)
				}
				usedNames[fieldName] = structType.Field(i).Name
				h = hashUpdateOrdered(w.h, h, fieldHash)
			}
		}
	}

	return h, nil
}

// hashUpdateOrdered combines two hash values in an order-dependent way.
// This is used for struct fields, array elements, and other cases where
// the order of elements matters for the final hash value.
func hashUpdateOrdered(h hash.Hash, a, b []byte) []byte {
	// For ordered updates, concatenate and hash
	h.Reset()
	_, _ = h.Write(a)
	_, _ = h.Write(b)
	return h.Sum(nil)
}

// hashUpdateUnordered combines two hash values in an order-independent way using XOR.
// This is used for map entries and set-like slices where the order of elements
// should not affect the final hash value. XOR is commutative, so a^b == b^a.
// Note: This function should always be followed by hashFinishUnordered to prevent
// XOR cancellation issues when the same hash appears multiple times.
func hashUpdateUnordered(a, b []byte) []byte {
	// For unordered updates, XOR the bytes (preserves commutativity)
	// Use the length of the first slice, assuming both are the same length
	if len(a) == 0 {
		return b
	}
	if len(b) == 0 {
		return a
	}

	minLen := min(len(a), len(b))

	result := make([]byte, minLen)
	for i := range minLen {
		result[i] = a[i] ^ b[i]
	}
	return result
}

// After mixing a group of unique hashes with hashUpdateUnordered, it's always
// necessary to call hashFinishUnordered. Why? Because hashUpdateUnordered
// is a simple XOR, and calling hashUpdateUnordered on hashes produced by
// hashUpdateUnordered can effectively cancel out a previous change to the hash
// result if the same hash value appears later on. For example, consider:
//
//	hashUpdateUnordered(hashUpdateUnordered("A", "B"), hashUpdateUnordered("A", "C")) =
//	H("A") ^ H("B")) ^ (H("A") ^ H("C")) =
//	(H("A") ^ H("A")) ^ (H("B") ^ H(C)) =
//	H(B) ^ H(C) =
//	hashUpdateUnordered(hashUpdateUnordered("Z", "B"), hashUpdateUnordered("Z", "C"))
//
// hashFinishUnordered "hardens" the result, so that encountering partially
// overlapping input data later on in a different context won't cancel out.
func hashFinishUnordered(h hash.Hash, a []byte) []byte {
	h.Reset()
	_, _ = h.Write(a)
	return h.Sum(nil)
}

// compareBytes compares two byte slices lexicographically.
// Returns -1 if a < b, 0 if a == b, 1 if a > b.
// This is used for sorting hash values to ensure deterministic ordering
// when processing slices marked with the "set" tag.
func compareBytes(a, b []byte) int {
	minLen := min(len(b), len(a))

	for i := range minLen {
		if a[i] < b[i] {
			return -1
		}
		if a[i] > b[i] {
			return 1
		}
	}

	if len(a) < len(b) {
		return -1
	}
	if len(a) > len(b) {
		return 1
	}
	return 0
}

// visitFlag is used as a bitmask for affecting visit behavior.
type visitFlag uint

const (
	visitFlagInvalid visitFlag = iota
	visitFlagSet               = iota << 1
)
