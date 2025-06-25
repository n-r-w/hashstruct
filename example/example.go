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

	_, _ = fmt.Printf("%x\n", hash) //nolint:forbidigo // ok for example
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

	_, _ = fmt.Printf("With options: %x\n", hashWithOptions) //nolint:forbidigo // ok for example
}
