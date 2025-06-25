package hashstruct

import (
	"bytes"
	"crypto/sha512"
	"encoding/hex"
	"errors"
	"hash/fnv"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestHash_identity(t *testing.T) {
	cases := []any{
		nil,
		"foo",
		42,
		true,
		false,
		[]string{"foo", "bar"},
		[]any{1, nil, "foo"},
		map[string]string{"foo": "bar"},
		map[any]string{"foo": "bar"},
		map[any]any{"foo": "bar", "bar": 0},
		struct {
			Foo string
			Bar []any
		}{
			Foo: "foo",
			Bar: []any{nil, nil, nil},
		},
		&struct {
			Foo string
			Bar []any
		}{
			Foo: "foo",
			Bar: []any{nil, nil, nil},
		},
	}

	for _, tc := range cases {
		// We run the test 100 times to try to tease out variability
		// in the runtime in terms of ordering.
		valuelist := make([][]byte, 100)
		for i := range valuelist {
			v, err := Hash(tc)
			require.NoError(t, err, "Error: %s\n\n%#v", err, tc)

			valuelist[i] = v
		}

		// Zero is always wrong
		assert.NotEmpty(t, valuelist[0], "zero hash: %#v", tc)

		// Make sure all the values match
		t.Logf("%#v: %x", tc, valuelist[0])
		for i := 1; i < len(valuelist); i++ {
			assert.True(t, bytes.Equal(valuelist[i], valuelist[0]), "non-matching: %d, %d\n\n%#v", i, 0, tc)
		}
	}
}

func TestHash_equal(t *testing.T) {
	type testFoo struct{ Name string }
	type testBar struct{ Name string }

	now := time.Now()

	cases := []struct {
		One, Two any
		Match    bool
	}{
		{
			map[string]string{"foo": "bar"},
			map[any]string{"foo": "bar"},
			true,
		},

		{
			map[string]any{"1": "1"},
			map[string]any{"1": "1", "2": "2"},
			false,
		},

		{
			struct{ Fname, Lname string }{"foo", "bar"},
			struct{ Fname, Lname string }{"bar", "foo"},
			false,
		},

		{
			struct{ Lname, Fname string }{"foo", "bar"},
			struct{ Fname, Lname string }{"foo", "bar"},
			false,
		},

		{
			struct{ Lname, Fname string }{"foo", "bar"},
			struct{ Fname, Lname string }{"bar", "foo"},
			false,
		},

		{
			testFoo{"foo"},
			testBar{"foo"},
			false,
		},

		{
			struct {
				Foo        string
				unexported string
			}{
				Foo:        "bar",
				unexported: "baz",
			},
			struct {
				Foo        string
				unexported string
			}{
				Foo:        "bar",
				unexported: "bang",
			},
			true,
		},

		{
			struct {
				testFoo
				Foo string
			}{
				Foo:     "bar",
				testFoo: testFoo{Name: "baz"},
			},
			struct {
				testFoo
				Foo string
			}{
				Foo: "bar",
			},
			true,
		},

		{
			struct {
				Foo string
			}{
				Foo: "bar",
			},
			struct {
				testFoo
				Foo string
			}{
				Foo: "bar",
			},
			true,
		},
		{
			now, // contains monotonic clock
			time.Date(now.Year(), now.Month(), now.Day(), now.Hour(),
				now.Minute(), now.Second(), now.Nanosecond(), now.Location()), // does not contain monotonic clock
			true,
		},
	}

	for i, tc := range cases {
		t.Run(strconv.Itoa(i), func(t *testing.T) {
			t.Logf("Hashing: %#v", tc.One)
			one, err := Hash(tc.One)
			t.Logf("Result: %x", one)
			require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

			t.Logf("Hashing: %#v", tc.Two)
			two, err := Hash(tc.Two)
			t.Logf("Result: %x", two)
			require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

			// Zero is always wrong
			assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

			// Compare
			assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
		})
	}
}

func TestHash_equalIgnore(t *testing.T) {
	type Test1 struct {
		Name string
		UUID string `hash:"ignore"`
	}

	type Test2 struct {
		Name string
		UUID string `hash:"-"`
	}

	type TestTime struct {
		Name string
		Time time.Time `hash:"string"`
	}

	type TestTime2 struct {
		Name string
		Time time.Time
	}

	now := time.Now()
	cases := []struct {
		One, Two any
		Match    bool
	}{
		{
			Test1{Name: "foo", UUID: "foo"},
			Test1{Name: "foo", UUID: "bar"},
			true,
		},

		{
			Test1{Name: "foo", UUID: "foo"},
			Test1{Name: "foo", UUID: "foo"},
			true,
		},

		{
			Test2{Name: "foo", UUID: "foo"},
			Test2{Name: "foo", UUID: "bar"},
			true,
		},

		{
			Test2{Name: "foo", UUID: "foo"},
			Test2{Name: "foo", UUID: "foo"},
			true,
		},
		{
			TestTime{Name: "foo", Time: now},
			TestTime{Name: "foo", Time: time.Time{}},
			false,
		},
		{
			TestTime{Name: "foo", Time: now},
			TestTime{Name: "foo", Time: now},
			true,
		},
		{
			TestTime2{Name: "foo", Time: now},
			TestTime2{Name: "foo", Time: time.Time{}},
			false,
		},
		{
			TestTime2{Name: "foo", Time: now},
			TestTime2{
				Name: "foo", Time: time.Date(now.Year(), now.Month(), now.Day(), now.Hour(),
					now.Minute(), now.Second(), now.Nanosecond(), now.Location()),
			},
			true,
		},
	}

	for _, tc := range cases {
		one, err := Hash(tc.One)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

		two, err := Hash(tc.Two)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

		// Zero is always wrong
		assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

		// Compare
		assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
	}
}

func TestHash_stringTagError(t *testing.T) {
	type Test1 struct {
		Name        string
		BrokenField string `hash:"string"`
	}

	type Test2 struct {
		Name        string
		BustedField int `hash:"string"`
	}

	type Test3 struct {
		Name string
		Time time.Time `hash:"string"`
	}

	cases := []struct {
		Test  any
		Field string
	}{
		{
			Test1{Name: "foo", BrokenField: "bar"},
			"BrokenField",
		},
		{
			Test2{Name: "foo", BustedField: 23},
			"BustedField",
		},
		{
			Test3{Name: "foo", Time: time.Now()},
			"",
		},
	}

	for _, tc := range cases {
		_, err := Hash(tc.Test)
		if err != nil {
			var ens *NotStringerError
			if errors.As(err, &ens) {
				assert.Equal(t, tc.Field, ens.Field, "did not get expected field %#v: got %s wanted %s", tc.Test, ens.Field, tc.Field)
			} else {
				require.Fail(t, "unknown error", "unknown error %#v: got %s", tc, err)
			}
		}
	}
}

func TestHash_equalNil(t *testing.T) {
	type Test struct {
		Str   *string
		Int   *int
		Map   map[string]string
		Slice []string
	}

	cases := []struct {
		One, Two any
		ZeroNil  bool
		Match    bool
	}{
		{
			Test{
				Str:   nil,
				Int:   nil,
				Map:   nil,
				Slice: nil,
			},
			Test{
				Str:   new(string),
				Int:   new(int),
				Map:   make(map[string]string),
				Slice: make([]string, 0),
			},
			true,
			true,
		},
		{
			Test{
				Str:   nil,
				Int:   nil,
				Map:   nil,
				Slice: nil,
			},
			Test{
				Str:   new(string),
				Int:   new(int),
				Map:   make(map[string]string),
				Slice: make([]string, 0),
			},
			false,
			false,
		},
		{
			nil,
			0,
			true,
			true,
		},
		{
			nil,
			0,
			false,
			true,
		},
	}

	for _, tc := range cases {
		one, err := Hash(tc.One, WithZeroNil(tc.ZeroNil))
		require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

		two, err := Hash(tc.Two, WithZeroNil(tc.ZeroNil))
		require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

		// Zero is always wrong
		assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

		// Compare
		assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
	}
}

func TestHash_equalSet(t *testing.T) {
	type Test struct {
		Name    string
		Friends []string `hash:"set"`
	}

	cases := []struct {
		One, Two any
		Match    bool
	}{
		{
			Test{Name: "foo", Friends: []string{"foo", "bar"}},
			Test{Name: "foo", Friends: []string{"bar", "foo"}},
			true,
		},

		{
			Test{Name: "foo", Friends: []string{"foo", "bar"}},
			Test{Name: "foo", Friends: []string{"foo", "bar"}},
			true,
		},
	}

	for _, tc := range cases {
		one, err := Hash(tc.One)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

		two, err := Hash(tc.Two)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

		// Zero is always wrong
		assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

		// Compare
		assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
	}
}

func TestHash_includable(t *testing.T) {
	cases := []struct {
		One, Two any
		Match    bool
	}{
		{
			testIncludable{Value: "foo"},
			testIncludable{Value: "foo"},
			true,
		},

		{
			testIncludable{Value: "foo", Ignore: "bar"},
			testIncludable{Value: "foo"},
			true,
		},

		{
			testIncludable{Value: "foo", Ignore: "bar"},
			testIncludable{Value: "bar"},
			false,
		},
	}

	for _, tc := range cases {
		one, err := Hash(tc.One)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

		two, err := Hash(tc.Two)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

		// Zero is always wrong
		assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

		// Compare
		assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
	}
}

func TestHash_ignoreZeroValue(t *testing.T) {
	cases := []struct {
		IgnoreZeroValue bool
	}{
		{
			IgnoreZeroValue: true,
		},
		{
			IgnoreZeroValue: false,
		},
	}
	structA := struct {
		Foo string
		Bar string
		Map map[string]int
	}{
		Foo: "foo",
		Bar: "bar",
	}
	structB := struct {
		Foo string
		Bar string
		Baz string
		Map map[string]int
	}{
		Foo: "foo",
		Bar: "bar",
	}

	for _, tc := range cases {
		hashA, err := Hash(structA, WithIgnoreZeroValue(tc.IgnoreZeroValue))
		require.NoError(t, err, "Failed to hash %#v: %s", structA, err)

		hashB, err := Hash(structB, WithIgnoreZeroValue(tc.IgnoreZeroValue))
		require.NoError(t, err, "Failed to hash %#v: %s", structB, err)

		assert.Equal(t, tc.IgnoreZeroValue, bytes.Equal(hashA, hashB), "bad, expected: %#v\n\n%x\n\n%x", tc.IgnoreZeroValue, hashA, hashB)
	}
}

func TestHash_includableMap(t *testing.T) {
	cases := []struct {
		One, Two any
		Match    bool
	}{
		{
			testIncludableMap{Map: map[string]string{"foo": "bar"}},
			testIncludableMap{Map: map[string]string{"foo": "bar"}},
			true,
		},

		{
			testIncludableMap{Map: map[string]string{"foo": "bar", "ignore": "true"}},
			testIncludableMap{Map: map[string]string{"foo": "bar"}},
			true,
		},

		{
			testIncludableMap{Map: map[string]string{"foo": "bar", "ignore": "true"}},
			testIncludableMap{Map: map[string]string{"bar": "baz"}},
			false,
		},
		{
			testIncludableMapMap{"foo": "bar"},
			testIncludableMapMap{"foo": "bar"},
			true,
		},

		{
			testIncludableMapMap{"foo": "bar", "ignore": "true"},
			testIncludableMapMap{"foo": "bar"},
			true,
		},

		{
			testIncludableMapMap{"foo": "bar", "ignore": "true"},
			testIncludableMapMap{"bar": "baz"},
			false,
		},
	}

	for _, tc := range cases {
		one, err := Hash(tc.One)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

		two, err := Hash(tc.Two)
		require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

		// Zero is always wrong
		assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

		// Compare
		assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
	}
}

func TestHash_hashable(t *testing.T) {
	cases := []struct {
		One, Two any
		Match    bool
		Err      string
	}{
		{
			testHashable{Value: "foo"},
			&testHashablePointer{Value: "foo"},
			true,
			"",
		},

		{
			testHashable{Value: "foo1"},
			&testHashablePointer{Value: "foo2"},
			true,
			"",
		},
		{
			testHashable{Value: "foo"},
			&testHashablePointer{Value: "bar"},
			false,
			"",
		},
		{
			testHashable{Value: "nofoo"},
			&testHashablePointer{Value: "bar"},
			true,
			"",
		},
		{
			testHashable{Value: "bar", Err: errors.New("oh no")},
			testHashable{Value: "bar"},
			true,
			"oh no",
		},
	}

	for i, tc := range cases {
		t.Run(strconv.Itoa(i), func(t *testing.T) {
			one, err := Hash(tc.One)
			if tc.Err != "" {
				require.Error(t, err, "expected error")
				assert.Contains(t, err.Error(), tc.Err, "expected error to contain %q, got: %s", tc.Err, err)
				return
			}
			require.NoError(t, err, "Failed to hash %#v: %s", tc.One, err)

			two, err := Hash(tc.Two)
			require.NoError(t, err, "Failed to hash %#v: %s", tc.Two, err)

			// Zero is always wrong
			assert.NotEmpty(t, one, "zero hash: %#v", tc.One)

			// Compare
			assert.Equal(t, tc.Match, bytes.Equal(one, two), "bad, expected: %#v\n\n%#v\n\n%#v", tc.Match, tc.One, tc.Two)
		})
	}
}

func TestHash_golden(t *testing.T) {
	foo := "foo"

	cases := []struct {
		In     any
		Expect string // hex string of expected hash
	}{
		{
			In:     nil,
			Expect: "af5570f5a1810b7af78caf4bc70a660f0df51e42baf91d4de5b2328de0e83dfc",
		},
		{
			In:     "foo",
			Expect: "2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae",
		},
		{
			In:     42,
			Expect: "ed049108bc18f2c64369e8d0ea42850bdd1a7d1dd340cfde716315579702a76c",
		},
		{
			In:     uint8(42),
			Expect: "684888c0ebb17f374298b65ee2807526c066094c701bcc7ebbe1c1095f494fc1",
		},
		{
			In:     int16(42),
			Expect: "17d5f5a33ab5f6aed0395d2bc0a4e5df61d92441ea8d77b0952c01bc8aa8bde0",
		},
		{
			In:     int32(42),
			Expect: "e8a4b2ee7ede79a3afb332b5b6cc3d952a65fd8cffb897f5d18016577c33d7cc",
		},
		{
			In:     int64(42),
			Expect: "ed049108bc18f2c64369e8d0ea42850bdd1a7d1dd340cfde716315579702a76c",
		},
		{
			In:     uint16(42),
			Expect: "17d5f5a33ab5f6aed0395d2bc0a4e5df61d92441ea8d77b0952c01bc8aa8bde0",
		},
		{
			In:     uint32(42),
			Expect: "e8a4b2ee7ede79a3afb332b5b6cc3d952a65fd8cffb897f5d18016577c33d7cc",
		},
		{
			In:     uint64(42),
			Expect: "ed049108bc18f2c64369e8d0ea42850bdd1a7d1dd340cfde716315579702a76c",
		},
		{
			In:     float32(42),
			Expect: "d1ee66cfef3186b736ab765972a0c0b5c59943027a64a352b9041bf7e3483182",
		},
		{
			In:     float64(42),
			Expect: "e726a50d216e6d71d7c53aabd23ab5e0d4677c3ef1f41fc35410143ebe6381c1",
		},
		{
			In:     complex64(42),
			Expect: "d6e2d009d05709755addd991435d866b800a3f7bfd259f0f836d691288613905",
		},
		{
			In:     complex128(42),
			Expect: "dcfe48f50126ab1ddf61ba17cea90988d493316f6330bc085fab929579f7999f",
		},
		{
			In:     true,
			Expect: "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
		},
		{
			In:     false,
			Expect: "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
		},
		{
			In:     []string{"foo", "bar"},
			Expect: "635c18b15ef5c5d6c020e72339ddefd8b05c4c4a44b34eff8cef226f89027702",
		},
		{
			In:     []any{1, nil, "foo"},
			Expect: "b6e77809edc95adf0385b368fcd23968ec9ad5369c0b9dd44927614f88e1443d",
		},
		{
			In:     map[string]string{"foo": "bar"},
			Expect: "06a4153bfe4e25a13aa95c27de8dc117c5d64384a355fe7e5a22dc1b0ffe43d3",
		},
		{
			In:     map[string]*string{"foo": &foo},
			Expect: "33790ff0c5b88a945c78369c8c7f889fcc4d0cb5fe86d92f86ca9ff5436ec6a1",
		},
		{
			In:     map[*string]string{&foo: "bar"},
			Expect: "06a4153bfe4e25a13aa95c27de8dc117c5d64384a355fe7e5a22dc1b0ffe43d3",
		},
		{
			In:     map[any]string{"foo": "bar"},
			Expect: "06a4153bfe4e25a13aa95c27de8dc117c5d64384a355fe7e5a22dc1b0ffe43d3",
		},
		{
			In:     map[any]any{"foo": "bar", "bar": 0},
			Expect: "5a78da0e73bc2904ecf223c8cfd51a0323dc48c6af48ffb44f852e298e140638",
		},
		{
			In:     map[any]any{"foo": "bar", "bar": map[any]any{"foo": "bar", "bar": map[any]any{"foo": "bar", "bar": map[any]any{&foo: "bar", "bar": 0}}}},
			Expect: "ce966b26c35e450f363ada499057ae7117f21d996a6f7e947c27a7e7cea3356f",
		},
		{
			In: struct {
				Foo string
				Bar []any
			}{
				Foo: "foo",
				Bar: []any{nil, nil, nil},
			},
			Expect: "b876d23a2d0965abd7a2448f391fa7a6968c72e56cb84560daa940e9ddc728e8",
		},
	}

	for i, tc := range cases {
		t.Run(strconv.Itoa(i), func(t *testing.T) {
			got, err := Hash(tc.In)
			require.NoError(t, err, "unexpected error: %s", err)

			gotHex := hex.EncodeToString(got)
			assert.Equal(t, tc.Expect, gotHex, "expected: %s, got: %s", tc.Expect, gotHex)
		})
	}
}

func TestHash_withTagName(t *testing.T) {
	// Test struct with multiple different custom tags on same fields
	type MyStruct struct {
		ID       int      `hashtag1:"ignore" hashtag2:"string"`
		Name     string   `hashtag1:"set" hashtag2:"ignore"`
		Values   []string `hashtag1:"string" hashtag2:"set"`
		Metadata string   // No custom tags, should always be included
	}

	testStruct := MyStruct{
		ID:       123,
		Name:     "test_name",
		Values:   []string{"a", "b", "c"},
		Metadata: "always_included",
	}

	// Hash with default tag name "hash" (no custom behavior)
	_, err := Hash(testStruct)
	require.NoError(t, err)

	// Hash with hashtag1 (ID ignored, Name as set, Values as string - will fail)
	_, err = Hash(testStruct, WithTagName("hashtag1"))
	require.Error(t, err, "Should fail because Values field has string tag but []string doesn't implement Stringer")
	var notStringerErr *NotStringerError
	require.ErrorAs(t, err, &notStringerErr)
	assert.Equal(t, "Values", notStringerErr.Field)

	// Hash with hashtag2 (ID as string - will fail, Name ignored, Values as set)
	_, err = Hash(testStruct, WithTagName("hashtag2"))
	require.Error(t, err, "Should fail because ID field has string tag but int doesn't implement Stringer")
	require.ErrorAs(t, err, &notStringerErr)
	assert.Equal(t, "ID", notStringerErr.Field)

	// Test with a struct that works with both tag systems
	type ValidStruct struct {
		ID       string    `hashtag1:"ignore" hashtag2:"-"`
		Name     string    `hashtag1:"set" hashtag2:"ignore"`
		Tags     []string  `hashtag1:"ignore" hashtag2:"set"`
		Created  time.Time `hashtag1:"string" hashtag2:"string"` // time.Time implements Stringer
		Metadata string    // No custom tags
	}

	now := time.Now()
	validStruct1 := ValidStruct{
		ID:       "id1",
		Name:     "test",
		Tags:     []string{"go", "test", "hash"},
		Created:  now,
		Metadata: "meta",
	}

	validStruct2 := ValidStruct{
		ID:       "id2",                          // Different but will be ignored in both tag systems
		Name:     "test",                         // Same
		Tags:     []string{"hash", "go", "test"}, // Different order
		Created:  now,                            // Same
		Metadata: "meta",                         // Same
	}

	// Hash with hashtag1: ID ignored, Name treated as set (but single value), Tags ignored, Created as string
	hash1_1, err := Hash(validStruct1, WithTagName("hashtag1"))
	require.NoError(t, err)

	hash1_2, err := Hash(validStruct2, WithTagName("hashtag1"))
	require.NoError(t, err)

	// Should be equal because ID is ignored, Name is same, Tags ignored, Created same, Metadata same
	assert.True(t, bytes.Equal(hash1_1, hash1_2), "Hashes should be equal with hashtag1")

	// Hash with hashtag2: ID ignored, Name ignored, Tags as set, Created as string
	hash2_1, err := Hash(validStruct1, WithTagName("hashtag2"))
	require.NoError(t, err)

	hash2_2, err := Hash(validStruct2, WithTagName("hashtag2"))
	require.NoError(t, err)

	// Should be equal because ID ignored, Name ignored, Tags as set (order doesn't matter), Created same, Metadata same
	assert.True(t, bytes.Equal(hash2_1, hash2_2), "Hashes should be equal with hashtag2")

	// The two different tag systems should produce different hashes
	assert.False(t, bytes.Equal(hash1_1, hash2_1), "Different tag systems should produce different hashes")
}

func TestHash_withSlicesAsSets(t *testing.T) {
	type TestStruct struct {
		Name    string
		Values  []string
		Numbers []int
	}

	test1 := TestStruct{
		Name:    "test",
		Values:  []string{"a", "b", "c"},
		Numbers: []int{1, 2, 3},
	}

	test2 := TestStruct{
		Name:    "test",
		Values:  []string{"c", "a", "b"}, // Different order
		Numbers: []int{3, 1, 2},          // Different order
	}

	// Hash without WithSlicesAsSets (should be different due to order)
	hash1, err := Hash(test1)
	require.NoError(t, err)

	hash2, err := Hash(test2)
	require.NoError(t, err)

	assert.False(t, bytes.Equal(hash1, hash2), "Hashes should be different when slice order matters")

	// Hash with WithSlicesAsSets (should be same despite order)
	hashSet1, err := Hash(test1, WithSlicesAsSets(true))
	require.NoError(t, err)

	hashSet2, err := Hash(test2, WithSlicesAsSets(true))
	require.NoError(t, err)

	assert.True(t, bytes.Equal(hashSet1, hashSet2), "Hashes should be equal when WithSlicesAsSets is true")
}

func TestHash_slicesAsSetsDuplicateIssue(t *testing.T) {
	// This test demonstrates the bug where slices with different duplicate items
	// produce the same hash when treated as sets due to XOR cancellation
	type TestStruct struct {
		Name   string
		Values []string
	}

	// Two clearly different lists with different duplicate elements
	test1 := TestStruct{
		Name:   "test",
		Values: []string{"a", "b", "c", "e", "e"}, // has duplicate "e"
	}

	test2 := TestStruct{
		Name:   "test",
		Values: []string{"a", "b", "c", "d", "d"}, // has duplicate "d"
	}

	// Hash with WithSlicesAsSets - these should be DIFFERENT but currently produce same hash
	hashSet1, err := Hash(test1, WithSlicesAsSets(true))
	require.NoError(t, err)

	hashSet2, err := Hash(test2, WithSlicesAsSets(true))
	require.NoError(t, err)

	// This assertion currently FAILS - demonstrating the bug
	// The slices contain different elements (one has "e", other has "d")
	// so they should have different hashes even when treated as sets
	assert.False(t, bytes.Equal(hashSet1, hashSet2),
		"BUG: Different slices with different duplicate elements should have different hashes when treated as sets")

	// Test with explicit set tag as well
	type TestStructWithSetTag struct {
		Name   string
		Values []string `hash:"set"`
	}

	testWithTag1 := TestStructWithSetTag{
		Name:   "test",
		Values: []string{"a", "b", "c", "e", "e"},
	}

	testWithTag2 := TestStructWithSetTag{
		Name:   "test",
		Values: []string{"a", "b", "c", "d", "d"},
	}

	hashTag1, err := Hash(testWithTag1)
	require.NoError(t, err)

	hashTag2, err := Hash(testWithTag2)
	require.NoError(t, err)

	// This should also be different
	assert.False(t, bytes.Equal(hashTag1, hashTag2),
		"BUG: Different slices with different duplicate elements should have different hashes with set tag")

	// Additional test cases to ensure comprehensive coverage

	// Test case: same elements but different number of duplicates
	test3 := TestStruct{
		Name:   "test",
		Values: []string{"a", "b", "c", "d"}, // no duplicates
	}

	test4 := TestStruct{
		Name:   "test",
		Values: []string{"a", "b", "c", "d", "d", "d"}, // multiple duplicates of "d"
	}

	hashSet3, err := Hash(test3, WithSlicesAsSets(true))
	require.NoError(t, err)

	hashSet4, err := Hash(test4, WithSlicesAsSets(true))
	require.NoError(t, err)

	// These should be equal because sets ignore duplicates
	assert.True(t, bytes.Equal(hashSet3, hashSet4),
		"Sets with same unique elements should have same hash regardless of duplicates")

	// Test case: empty slice vs slice with duplicates that cancel out
	test5 := TestStruct{
		Name:   "test",
		Values: []string{}, // empty
	}

	// This would have been problematic with the old XOR approach
	// if we had elements that XOR to zero
	hashSet5, err := Hash(test5, WithSlicesAsSets(true))
	require.NoError(t, err)

	// Should be different from any non-empty set
	assert.False(t, bytes.Equal(hashSet1, hashSet5),
		"Empty set should have different hash from non-empty set")
}

func TestHash_withUseStringer(t *testing.T) {
	// First test with a non-Stringer type to show normal behavior
	type NonStringer struct {
		Internal string // Exported field
		Display  string // Exported field
	}

	type TestWithNonStringer struct {
		Name  string
		Value NonStringer
	}

	nonStringer1 := TestWithNonStringer{
		Name:  "test",
		Value: NonStringer{Internal: "different1", Display: "same"},
	}

	nonStringer2 := TestWithNonStringer{
		Name:  "test",
		Value: NonStringer{Internal: "different2", Display: "same"},
	}

	// Without WithUseStringer, should be different due to internal field
	hashNormal1, err := Hash(nonStringer1)
	require.NoError(t, err)

	hashNormal2, err := Hash(nonStringer2)
	require.NoError(t, err)

	assert.False(t, bytes.Equal(hashNormal1, hashNormal2), "Should be different when internal fields differ")

	// Now test with actual Stringer implementation
	type TestWithStringer struct {
		Name     string
		Stringer actualTestStringer
	}

	stringer1 := TestWithStringer{
		Name:     "test",
		Stringer: actualTestStringer{Internal: "different1", Display: "same"},
	}

	stringer2 := TestWithStringer{
		Name:     "test",
		Stringer: actualTestStringer{Internal: "different2", Display: "same"},
	}

	// Without WithUseStringer, ActualStringer fields are hashed normally (should be different)
	hashStringerNormal1, err := Hash(stringer1)
	require.NoError(t, err)

	hashStringerNormal2, err := Hash(stringer2)
	require.NoError(t, err)

	assert.False(t, bytes.Equal(hashStringerNormal1, hashStringerNormal2), "Should be different when ActualStringer internal fields differ")

	// With WithUseStringer, should be same due to String() method
	hashWithStringer1, err := Hash(stringer1, WithUseStringer(true))
	require.NoError(t, err)

	hashWithStringer2, err := Hash(stringer2, WithUseStringer(true))
	require.NoError(t, err)

	assert.True(t, bytes.Equal(hashWithStringer1, hashWithStringer2), "Should be equal when String() output is same")

	// Test with different String() output
	stringer3 := TestWithStringer{
		Name:     "test",
		Stringer: actualTestStringer{Internal: "same", Display: "display1"},
	}

	stringer4 := TestWithStringer{
		Name:     "test",
		Stringer: actualTestStringer{Internal: "same", Display: "display2"},
	}

	// With WithUseStringer, should be different due to different String() output
	hashWithStringer3, err := Hash(stringer3, WithUseStringer(true))
	require.NoError(t, err)

	hashWithStringer4, err := Hash(stringer4, WithUseStringer(true))
	require.NoError(t, err)

	assert.False(t, bytes.Equal(hashWithStringer3, hashWithStringer4), "Should be different when String() output differs")
}

// actualTestStringer is a test type that implements fmt.Stringer
type actualTestStringer struct {
	Internal string // Exported field
	Display  string // Exported field
}

// String implements fmt.Stringer
func (a actualTestStringer) String() string {
	return a.Display
}

func BenchmarkMap(b *testing.B) {
	m := map[string]any{
		"int16":      int16(42),
		"int32":      int32(42),
		"int64":      int64(42),
		"int":        int(42),
		"uint16":     uint16(42),
		"uint32":     uint32(42),
		"uint64":     uint64(42),
		"uint":       uint(42),
		"float32":    float32(42),
		"float64":    float64(42),
		"complex64":  complex64(42),
		"complex128": complex128(42),
		"string":     "foo",
		"bool":       true,
		"slice":      []string{"foo", "bar"},
		"sliceint":   []int{1, 2, 3},
		"map":        map[string]string{"foo": "bar"},
		"struct": struct {
			Foo string
			Bar []any
		}{
			Foo: "foo",
			Bar: []any{nil, nil, nil},
		},
	}

	for range b.N {
		_, _ = Hash(m)
	}
}

func TestHash_customHasherSizes(t *testing.T) {
	testData := map[string][]string{
		"key1": {"value1", "value2"},
		"key2": {"value3", "value4"},
		"key3": {"value5", "value6"},
	}

	// Test with default SHA256 (32 bytes)
	hashSHA256, err := Hash(testData)
	require.NoError(t, err)
	assert.Len(t, hashSHA256, 32, "SHA256 should produce 32-byte hash")

	// Test with sha256 (default - 32 bytes)
	hashXXHash, err := Hash(testData)
	require.NoError(t, err)
	assert.Len(t, hashXXHash, 8, "xxhash should produce 8-byte hash")

	// Test with SHA512 (64 bytes)
	hashSHA512, err := Hash(testData, WithHasher(sha512.New()))
	require.NoError(t, err)
	assert.Len(t, hashSHA512, 64, "SHA512 should produce 64-byte hash")

	// The hashes should be different (different algorithms)
	assert.False(t, bytes.Equal(hashSHA256, hashXXHash), "SHA256 and xxhash should produce different results")
	assert.False(t, bytes.Equal(hashSHA256, hashSHA512), "SHA256 and SHA512 should produce different results")

	// Test consistency - same hasher should produce same result
	hashXXHash2, err := Hash(testData)
	require.NoError(t, err)
	assert.True(t, bytes.Equal(hashXXHash, hashXXHash2), "Same hasher should produce consistent results")
}

func BenchmarkString(b *testing.B) {
	s := "lorem ipsum dolor sit amet"

	b.Run("default (sha256)", func(b *testing.B) {
		for range b.N {
			_, _ = Hash(s)
		}
	})

	b.Run("sha512", func(b *testing.B) {
		for range b.N {
			_, _ = Hash(s, WithHasher(sha512.New()))
		}
	})

	b.Run("fnv", func(b *testing.B) {
		for range b.N {
			_, _ = Hash(s, WithHasher(fnv.New64a()))
		}
	})
}

type testIncludable struct {
	Value  string
	Ignore string
}

func (t testIncludable) HashInclude(field string, v any) (bool, error) {
	return field != "Ignore", nil
}

type testIncludableMap struct {
	Map map[string]string
}

func (t testIncludableMap) HashIncludeMap(field string, k, v any) (bool, error) {
	if field != "Map" {
		return true, nil
	}

	if s, ok := k.(string); ok && s == "ignore" {
		return false, nil
	}

	return true, nil
}

type testHashable struct {
	Value string
	Err   error
}

func (t testHashable) Hash() ([]byte, error) {
	if t.Err != nil {
		return nil, t.Err
	}

	if strings.HasPrefix(t.Value, "foo") {
		return []byte{500 % 256, 500 / 256}, nil
	}

	return []byte{100}, nil
}

type testHashablePointer struct {
	Value string
}

func (t *testHashablePointer) Hash() ([]byte, error) {
	if strings.HasPrefix(t.Value, "foo") {
		return []byte{500 % 256, 500 / 256}, nil
	}

	return []byte{100}, nil
}

type testIncludableMapMap map[string]string

func (t testIncludableMapMap) HashIncludeMap(_ string, k, _ any) (bool, error) {
	return k.(string) != "ignore", nil
}
