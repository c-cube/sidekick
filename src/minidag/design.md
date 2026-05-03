

# minidag

A serialization format intended to be a trimmed-down, minimalistic version of [twine](https://twine-data.dev/)
focusing on extensibility.

We define a basic set of primitive types (scalars), a notion of _reference_ (pointer to a value coming
earlier in the byte stream), and a notion of _command_ (which builds a composite value out of scalars and
references to other values). The set of commands is user defined and provides extensibility;
the builtin scalars and references provide a uniform representation that allow tools to process
_any_ DAG in the same fashion (e.g. reachability analysis, display, or pruning).

## data model

The actual data model is user-defined, but must be expressible in terms of DAG nodes.
Each node has a _command_, and a list of scalar arguments.

In other words, the bytestream contains a DAG, whose nodes have the form
`(<command> <scalar>*)`.

Scalars comprise: `null`, booleans, int64 numbers, float32/float64, (UTF-8) strings, binary blobs,
and the notion of _reference_ (an absolute offset in the bytestream, which point to earlier to ensure
acyclicity).

For example, lambda terms of the Simple Type Theory are represented by:

```
term := Var var | Lambda var term | Apply term term
var := { name: string, type: type }
type := Type_const name | Arrow type type
```

This can be defined with the following set of commands, where `@x` is a reference
a command returning type `x`:

```
"term.var" @var  // returns term
"term.app" @term @term  // returns term
"term.lambda" @var @term  // returns term

"var" string @type  // returns var

"type.const" string // returns type
"type.arrow" @type @type // returns type
```

## Wire format

The format is designed to be read forward or backward.

- forward: the byte stream is just a sequence of nodes, read in the same
    order they were produced.
- backward: starting from a byte offset that is of interest (eg the
    proof of "false" in a refutational prover), traverse the DAG backward
    by following references. This can allow tools to touch only a fraction of the
    nodes in the stream.


Each node is made of a list of scalars, followed by `0x00` (the stop marker).
The first scalar is normally a string that represents the _command_; the other scalars
are the command's arguments.

Scalars are represented by a _leading byte_. The leading byte contains the scalar's
type, and some length or integer value information:

```
  [ tag: 3 bits | padding: 1 bit | embedded integer: 4 bits ]

    ^--- high nibble ----------^   ^---- low nibble -------^
```

Tags are as follow:

- 0: stop (coincides with `0x00` being stop)
- 1: special (null=0, true=1, false=2)
- 2: non-negative integer, up to 64 bits. See later for where the data is.
- 3: negative integer, up to -2^63 (min int64).
- 4: float, 32 or 64 bits
- 5: string (UTF-8). The integer data is the byte length.
- 6: blob (raw binary). The integer data is the byte length.
- 7: reference. The integer data is the absolute offset in the stream.

The integer data associated with the scalar is represented in the low nibble.

- values from 0 to 11 represent themselves (ie low nibble=3 represents the embedded
    integer 3). Values above this indicate the number of additional bytes, immediately
    following the leading byte, and that contain the actul value.
- value 12: 1 byte follows, the value is that u8
- value 13: 2 bytes follow, the value is that u16 (little endian)
- value 14: 4 bytes follow, the value is that u32 (little endian)
- value 15: 8 bytes follow, the value is that u64 (little endian)

Each scalar type does a different thing with this embedded integer.
- stop/null: no integer (must be 0)
- bool: 0 is false, 1 is true
- non-negative integer: it's the value.
- negative integers: encode the absolute value
- floats: value is 14 or 15, followed by the 32- or 64-bits representation of the float.
- strings and blobs: the embedded integer is the number of bytes that follow with the data.
- reference: value is the absolute offset referred to

So the string "hello" would be: `0x55 'h' 'e' 'l' 'l' 'o'`.
Integer `8 : u64` is `0x28`, integer `39 : u64` is `0x2c 39`.
a 64kiB (=0x10000 bytes) png blob would be `0x6e 0x00 0x01 0x00 0x00 <the png bytes>`.



