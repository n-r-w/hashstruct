package hashstruct

import (
	"fmt"
)

// NotStringerError is returned when there's an error with hash:"string".
type NotStringerError struct {
	Field string
}

// Error implements error for NotStringerError.
func (ens *NotStringerError) Error() string {
	return fmt.Sprintf("hashstruct: %s has hash:\"string\" set, but does not implement fmt.Stringer", ens.Field)
}

// NotTimeError is returned when there's an error with hash:"utc".
type NotTimeError struct {
	Field string
}

// Error implements error for NotTimeError.
func (ent *NotTimeError) Error() string {
	return fmt.Sprintf("hashstruct: %s has hash:\"utc\" set, but is not of type time.Time", ent.Field)
}

// FormatError is returned when an invalid format is given to the Hash function.
type FormatError struct{}

func (*FormatError) Error() string {
	return "format must be one of the defined Format values in the hashstruct library"
}
