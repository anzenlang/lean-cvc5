# Lean cvc5 FFI

## Overview

The Lean cvc5 is a Foreign Function Interface (FFI) library that provides a minimal interface to the
cvc5 solver in Lean. It was designed to support the needs of the
[lean-smt] tactic. The FFI allows Lean programs to interact
with cvc5 by calling its functions and accessing its API.

## Getting Started

To use `lean-smt` in your project, add the following lines to your list of
dependencies in `lakefile.toml`:
```toml
[[require]]
name = "smt"
scope = "abdoo8080"
rev = "573fd67"
```

If your build configuration is in `lakefile.lean`, add the following line to
your dependencies:
```lean
require cvc5 from git "https://github.com/abdoo8080/lean-cvc5.git" @ "573fd67"
```

## Building

Build artifacts are available for all platforms supported by Lean 4 and
recent versions of Lean 4's toolchain. Choose the appropriate build for your
platform from the [releases page](https://github.com/abdoo8080/lean-cvc5/releases).
To build from source, you need to have `clang` and `libc++` (version 19) installed on
your system. If you are using Windows, you need to have `clang` and `libc++`
(version 19) installed on your `MSYS2` environment. Build this library by running
`lake build` in the root directory of the project.

## Missing features

Term API:

- [`getStringValue`](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5.h#L1600-L1607)

Solver API:

- [statistics](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5.h#L3410-L3425)
- [option info](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5.h#L3240-L3279)
- [driver options](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5.h#L3211-L3223)
- [plugins](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5.h#L3616-L3619)

Input parser:

- [`setStreamInput`](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5_parser.h#L251-L259)
- [dedicated parser errors](https://github.com/cvc5/cvc5/blob/cf59add20e053647145edb5f8151a2785c1d703e/include/cvc5/cvc5_parser.h#L348-L352)

## Contributing

Contributions to the Lean cvc5 FFI project are welcome! If you would like to contribute, please
follow these guidelines:

1. Fork the repository
2. Create a new branch for your feature or bug fix
    <!-- 3. Make your changes and ensure all tests pass -->
3. Submit a pull request with a clear description of your changes

[lean-smt]: https://github.com/ufmg-smite/lean-smt
