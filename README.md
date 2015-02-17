# snårkl ("Snorkel")

An Embedded DSL for Verifiable Computing

## Build

snårkl builds with GHC version >= 7.8.3. It may compile with earlier versions as well, but this hasn't been tested.

```
> cd src
> make
```
## Examples

[Main.hs](https://github.com/gstew5/snarkl/blob/master/src/Main.hs) contains some small snårkl programs, used for testing purposes. [app/keccak/Main.hs](https://github.com/gstew5/snarkl/blob/master/src/app/keccak/Main.hs), which can be built by

```
> make keccak
```

from the `src` directory, contains a basic implementation of the Keccak (SHA3) round function, for lane width 1.
