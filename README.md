# Truss

Truss is a programming language. This repository holds its standard library
and stage0, its compiler, which is written in OCaml.

## Building the compiler

With opam and a switch of OCaml 5.5 or later, install the dependencies:

```sh
opam install . --deps-only --with-test --with-dev-setup
```

`--with-test` installs menhir, which the test suites' reference parser needs.
`--with-dev-setup` installs the ocamlformat version that `dune build @fmt`
checks against.

Build every library, executable, and test suite:

```sh
eval $(opam env)
dune build
```

To build only the `truss` executable, name its target:

```sh
dune build stage0/driver/truss/truss.exe
```

The executable is `_build/default/stage0/driver/truss/truss.exe`.

## Building the documentation

The documentation is odoc's pages for the stage0 libraries, with graphs of
the libraries' dependencies. It needs odoc, dune-deps, and Graphviz:

```sh
opam install odoc dune-deps
brew install graphviz
```

On Linux, install Graphviz from the system's package manager instead, such
as `apt install graphviz`.

Build it:

```sh
stage0/tools/docs/build.sh
```

The script prints the absolute path of the index page,
`_build/docs/index.html`.
