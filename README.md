# hashstruct [![GoDoc](https://godoc.org/github.com/n-r-w/hashstruct?status.svg)](https://godoc.org/github.com/n-r-w/hashstruct)

hashstruct is a Go library for creating a unique SHA256 hash value
for arbitrary values in Go.

This can be used to key values in a hash (for use in a map, set, etc.)
that are complex. The most common use case is comparing two values without
sending data across the network, caching values locally (de-dup), and so on.

## Features

  * Hash any arbitrary Go value, including complex types.

  * Tag a struct field to ignore it and not affect the hash value.

  * Tag a slice type struct field to treat it as a set where ordering
    doesn't affect the hash code but the field itself is still taken into
    account to create the hash value.

  * Use `name` tags to protect hash values from field renaming during refactoring.

  * Optionally, specify a custom hash function to optimize for speed, collision
    avoidance for your data set, etc.

  * Optionally, hash the output of `.String()` on structs that implement fmt.Stringer,
    allowing effective hashing of time.Time

  * Optionally, override the hashing process by implementing `Hashable`.

## Installation

Standard `go get`:

```
$ go get github.com/n-r-w/hashstruct
```

## Usage & Example

For usage and examples see the [Godoc](http://godoc.org/github.com/n-r-w/hashstruct).

A quick code example is shown below:

```go
package main

import (
	"fmt"

	"github.com/n-r-w/hashstruct"
)

func main() {
	const exampleAge = 64

	type ComplexStruct struct {
		Name     string
		Age      uint
		Metadata map[string]any
	}

	v := ComplexStruct{
		Name: "mitchellh",
		Age:  exampleAge,
		Metadata: map[string]any{
			"car":      true,
			"location": "California",
			"siblings": []string{"Bob", "John"},
		},
	}

	// Hash with default options
	hash, err := hashstruct.Hash(v)
	if err != nil {
		panic(err)
	}

	_, _ = fmt.Printf("%x", hash) //nolint:forbidigo // ok for example
	// Output:
	// 1f348fbdb095b37ce74d8a416efcb82241e88a77501ebe2d387cfe450f08596e

	// Hash with custom options using optional func pattern
	hashWithOptions, err := hashstruct.Hash(v,
		hashstruct.WithZeroNil(true),
		hashstruct.WithIgnoreZeroValue(true),
	)
	if err != nil {
		panic(err)
	}

	_, _ = fmt.Printf("With options: %x", hashWithOptions) //nolint:forbidigo // ok for example
}
```

## Configuration Options

The `Hash` function accepts optional configuration parameters using the functional options pattern:

### `WithHasher(h hash.Hash)`
Sets a custom hash function. Default is SHA256.
```go
import "crypto/sha512"
hash, err := hashstruct.Hash(data, hashstruct.WithHasher(sha512.New()))
```

### `WithTagName(name string)`
Changes the struct tag name from default "hash" to a custom name.
```go
type User struct {
    ID int64 `myhash:"ignore"`
}
hash, err := hashstruct.Hash(user, hashstruct.WithTagName("myhash"))
```

### `WithZeroNil(bool)`
Treats nil pointers equal to zero values of the pointed type.
```go
// nil *int and int(0) will produce the same hash
hash, err := hashstruct.Hash(data, hashstruct.WithZeroNil(true))
```

### `WithIgnoreZeroValue(bool)`
Ignores fields with zero values (0, "", nil, etc.) in hash calculation.
```go
// Only non-zero fields affect the hash
hash, err := hashstruct.Hash(data, hashstruct.WithIgnoreZeroValue(true))
```

### `WithSlicesAsSets(bool)`
Treats all slices as unordered sets (same as adding `hash:"set"` to every slice field).
```go
// [1,2,3] and [3,1,2] produce the same hash
hash, err := hashstruct.Hash(data, hashstruct.WithSlicesAsSets(true))
```

### `WithUseStringer(bool)`
Uses `String()` method for any field implementing `fmt.Stringer`.
```go
// All fmt.Stringer fields use their String() representation
hash, err := hashstruct.Hash(data, hashstruct.WithUseStringer(true))
```

## Struct Tags Reference

You can control how struct fields are hashed using struct tags. The default tag name is `hash`, but this can be changed using the `WithTagName` option.

### Basic Usage

```go
type User struct {
    ID       int64     `hash:"ignore"`      // This field won't affect the hash
    Name     string                         // This field will be included normally
    Email    string    `hash:"-"`           // Alternative way to ignore a field
    Tags     []string  `hash:"set"`         // Treat this slice as an unordered set
    Created  time.Time `hash:"string"`      // Use the String() method for hashing
    Updated  time.Time `hash:"utc"`         // Convert to UTC before hashing
    Field1   int       `hash:"name=Field1"` // Override field name in hash
    Field2   int       `hash:"Field2"`      // Shorthand name override
}
```

### Available Tags

**⚠️ Important:** Use only the exact tag values and syntax listed below. Tags can be combined with commas (e.g., `hash:"name=field,utc"`). Note that `name:` (with colon) is not supported - use `name=` (with equals) instead.

### Tag Reference

#### `ignore` or `-`

Excludes the field from hash calculation entirely.

```go
type Config struct {
    DatabaseURL string `hash:"ignore"` // Sensitive data, don't include in hash
    Debug       bool   `hash:"-"`      // Alternative syntax
    AppName     string                 // This will be included
}
```

**Use cases:**
- Sensitive information (passwords, API keys, database URLs)
- Frequently changing metadata that shouldn't affect equality
- Internal bookkeeping fields

#### `set`

Treats slices as unordered sets where element order doesn't affect the hash value.

```go
type Document struct {
    Title string
    Tags  []string `hash:"set"` // ["go", "programming"] == ["programming", "go"]
}

// These will produce the same hash:
doc1 := Document{Title: "Guide", Tags: []string{"go", "tutorial"}}
doc2 := Document{Title: "Guide", Tags: []string{"tutorial", "go"}}
```

**Use cases:**
- Tag lists where order doesn't matter
- Permission sets
- Feature flags
- Any collection where you care about membership, not order

#### `string`

Uses the field's `String()` method (fmt.Stringer interface) for hashing instead of the field's internal representation.

```go
type Event struct {
    Name      string
    Timestamp time.Time `hash:"string"` // Uses time.Time.String() method
}
```

**Use cases:**
- `time.Time` fields (recommended for consistent hashing across time zones)
- Custom types that implement `fmt.Stringer`
- When you want a human-readable representation to determine equality

**Note:** If a field has the `string` tag but doesn't implement `fmt.Stringer`, the Hash function will return a `NotStringerError`.

#### `utc`

Converts `time.Time` fields to UTC before hashing. This ensures that times representing the same moment but in different timezones produce the same hash.

```go
type Event struct {
    Name      string
    Timestamp time.Time `hash:"utc"` // Converts to UTC before hashing
}

// These will produce the same hash:
utc := time.Date(2023, 1, 1, 12, 0, 0, 0, time.UTC)
est := utc.In(time.FixedZone("EST", -5*3600)) // Same moment, different timezone

event1 := Event{Name: "Meeting", Timestamp: utc}
event2 := Event{Name: "Meeting", Timestamp: est}
```

**Use cases:**
- When you want timezone-independent hashing of timestamps
- Comparing events that may be recorded in different timezones
- Ensuring consistent hashing across systems in different regions

**Note:** If a field has the `utc` tag but is not of type `time.Time`, the Hash function will return a `NotTimeError`.

#### `name=<fieldname>` or `<fieldname>`

Override the field name used in the hash calculation. This protects against field renaming during refactoring.

```go
type MyStruct struct {
    Field1 int `hash:"name=Field1"` // Explicit syntax
    Field2 int `hash:"Field2"`      // Shorthand syntax
}

// After refactoring field names, hash remains the same:
type MyStruct struct {
    RenamedField1 int `hash:"name=Field1"` // Same hash as before
    RenamedField2 int `hash:"Field2"`      // Same hash as before
}
```

**Use cases:**
- Protecting against field renaming during refactoring
- Maintaining backward compatibility when evolving struct definitions
- Consistent hashing across different versions of a struct

**Important:** Multiple fields cannot use the same hash field name - this will cause an error.

#### Combining with Other Tags

```go
type Event struct {
    Date time.Time `hash:"name=eventDate,utc"` // Custom name + UTC conversion
    Tags []string  `hash:"categories,set"`     // Shorthand name + set behavior
}
```

### Advanced Examples

#### Combining Tags with Options

```go
type Product struct {
    ID          int64     `hash:"ignore"`
    Name        string
    Categories  []string  `hash:"set"`
    CreatedAt   time.Time `hash:"string"`
    UpdatedAt   time.Time `hash:"utc"`
    DeletedAt   time.Time `hash:"ignore"`
}

// Hash with custom options
hash, err := hashstruct.Hash(product,
    hashstruct.WithIgnoreZeroValue(true), // Skip zero-value fields
    hashstruct.WithTagName("myhash"),     // Use "myhash" instead of "hash"
)
```

#### Custom Tag Names

```go
type User struct {
    ID   int64  `myhash:"ignore"`
    Name string
}

hash, err := hashstruct.Hash(user, hashstruct.WithTagName("myhash"))
```

### Custom Interfaces

For advanced control over hashing behavior, you can implement these interfaces:

#### `Hashable`

Override the entire hash calculation for a struct:

```go
type CustomStruct struct {
    Data string
}

func (c CustomStruct) Hash() ([]byte, error) {
    return hashstruct.Hash(strings.ToLower(c.Data))
}
```

#### `Includable`

Control which fields are included in the hash:

```go
func (u User) HashInclude(field string, v any) (bool, error) {
    // Only include non-empty string fields
    if s, ok := v.(string); ok {
        return s != "", nil
    }
    return true, nil
}
```

#### `IncludableMap`

Control which map entries are included:

```go
func (c Config) HashIncludeMap(field string, k, v any) (bool, error) {
    // Skip entries with "internal_" prefix
    if key, ok := k.(string); ok {
        return !strings.HasPrefix(key, "internal_"), nil
    }
    return true, nil
}
```

## Difference from parent project

Based on https://github.com/mitchellh/hashstructure.
This library returns `[]byte` SHA256 hashes by default instead of `uint64` values,
providing better collision resistance and cryptographic properties. In addition,
this library supports custom hash functions.
