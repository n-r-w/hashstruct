package hashstruct

import (
	"crypto/sha256"
	"hash"
)

// Option configures the hashing behavior.
type Option func(*config)

// WithHasher sets the hash function to use. By default, SHA256 is used.
// You might want to use a different hasher for performance reasons or to match
// existing hash requirements in your system.
func WithHasher(h hash.Hash) Option {
	return func(c *config) {
		c.hasher = h
	}
}

// WithTagName sets the struct tag to look at when hashing the structure.
// By default, the "hash" tag is used. You might want to change this if you're
// using a different tag name or if "hash" conflicts with other libraries.
func WithTagName(name string) Option {
	return func(c *config) {
		c.tagName = name
	}
}

// WithZeroNil sets whether nil pointer should be treated equal to a zero value of pointed type.
// When true, a nil *int and an int with value 0 will produce the same hash.
// When false (default), nil pointers and zero values produce different hashes.
func WithZeroNil(zeroNil bool) Option {
	return func(c *config) {
		c.zeroNil = zeroNil
	}
}

// WithIgnoreZeroValue sets whether zero value fields should be ignored for hash calculation.
// When true, fields with zero values (0, "", nil, etc.) are not included in the hash.
// This is useful when you want to hash only the "meaningful" data in a struct.
func WithIgnoreZeroValue(ignore bool) Option {
	return func(c *config) {
		c.ignoreZeroValue = ignore
	}
}

// WithSlicesAsSets sets whether to assume that a `set` tag is always present for slices.
// When true, all slices are treated as unordered sets where [1,2,3] and [3,1,2]
// produce the same hash. When false (default), slice order matters unless the
// field has an explicit "set" tag.
func WithSlicesAsSets(asSets bool) Option {
	return func(c *config) {
		c.slicesAsSets = asSets
	}
}

// WithUseStringer sets whether to attempt to use fmt.Stringer always.
// When true, any field that implements fmt.Stringer will be hashed using its
// String() method. If a field has both this option enabled and a "string" tag,
// the tag takes precedence. If the field doesn't implement fmt.Stringer and
// has a "string" tag, an error is returned.
func WithUseStringer(useStringer bool) Option {
	return func(c *config) {
		c.useStringer = useStringer
	}
}

// config holds the internal configuration for hashing.
type config struct {
	// hasher is the hash function to use. If this isn't set, it will
	// default to SHA256.
	hasher hash.Hash

	// tagName is the struct tag to look at when hashing the structure.
	// By default this is "hash".
	tagName string

	// zeroNil is flag determining if nil pointer should be treated equal
	// to a zero value of pointed type. By default this is false.
	zeroNil bool

	// ignoreZeroValue is determining if zero value fields should be
	// ignored for hash calculation.
	ignoreZeroValue bool

	// slicesAsSets assumes that a `set` tag is always present for slices.
	// Default is false (in which case the tag is used instead)
	slicesAsSets bool

	// useStringer will attempt to use fmt.Stringer always. If the struct
	// doesn't implement fmt.Stringer, it'll fall back to trying usual tricks.
	// If this is true, and the "string" tag is also set, the tag takes
	// precedence (meaning that if the type doesn't implement fmt.Stringer, we
	// panic)
	useStringer bool
}

// defaultConfig returns a config with default values.
func defaultConfig() *config {
	return &config{
		hasher:          sha256.New(),
		tagName:         "hash",
		zeroNil:         false,
		ignoreZeroValue: false,
		slicesAsSets:    false,
		useStringer:     false,
	}
}
