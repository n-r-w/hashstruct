package hashstruct

// Includable is an interface that can optionally be implemented by
// a struct. It will be called for each field in the struct to check whether
// it should be included in the hash.
type Includable interface {
	HashInclude(field string, v any) (bool, error)
}

// IncludableMap is an interface that can optionally be implemented by
// a struct. It will be called when a map-type field is found to ask the
// struct if the map item should be included in the hash.
type IncludableMap interface {
	HashIncludeMap(field string, k, v any) (bool, error)
}

// Hashable is an interface that can optionally be implemented by a struct
// to override the hash value. This value will override the hash value for
// the entire struct. Entries in the struct will not be hashed.
type Hashable interface {
	Hash() ([]byte, error)
}
