# Truss Packages

This document defines packages, projects, manifests, the lock file, and the
registry. [SPECIFICATION.md](SPECIFICATION.md) defines the language, and
[DESIGN.md](DESIGN.md#packages) gives the reasons for these rules.

## Packages

A package is a directory with a `truss.toml` manifest that has a `[package]`
table. Every directory under it that holds a `.truss` file is one of its
modules, and the files of a directory share one namespace (see
[Module paths](SPECIFICATION.md#module-paths)).

A package is the reach of `internal` and of `opaque`, where a type's methods
and a trait's `impl`s may live, the unit a manifest grants capabilities to,
and the unit that is published and given a version.

| Kind | Named | Its code | Its version |
|---|---|---|---|
| The standard library | `standard` | Part of the toolchain | The toolchain's |
| A project's own | Its manifest's name | Under the project's directory | None |
| From the registry | `owner::name` | Fetched, and kept by the hash of its content | In the project's lock file |

A package's program starts at the `main` of its root module, the files
beside the manifest, such as `main.truss`. A package whose root module has
no `main` is a library.

### Package names

- A package's name is a `lower_snake_case` name, or two joined by `::`, an
  owner and a name, as in `acme::geometry`. An owner is an account on the
  registry, and only its owner publishes under it.
- A package has an owner in its name to be published. A project's own
  package may have a name of one part, such as `weather`. A name of one part
  cannot be the owner of another package of the build.
- `standard` is the standard library. The owner `truss` is the Truss
  project's, and its packages are the approved packages, such as
  `truss::postgres`.
- A name in code is the registry's name: a package cannot be given another
  name.
- The registry never hands a name, or an owner, to another account, and never
  removes or replaces a published version.

## Package manifest

A package's manifest, `truss.toml`, names the package, says which Truss it is
written for, and lists the packages its code may use, each with the
capabilities it is granted:

```toml
[package]
name = "weather"
truss = "0.1"

[dependencies]
forecast = []
"truss::postgres" = ["NetworkClient", "Handles", "Clock"]
```

- **`name`** is the package's name.
- **`truss`** is the language version the package's files are read as, and
  the least toolchain that can build it. A toolchain reads each package as
  the version it names, so packages written for different versions build
  together.
- **Each entry of `[dependencies]`** is a package's name and the list of
  capabilities it is granted. A prelude capability is written by its name,
  and any other by its full path, as in
  `"acme::store::connection::ReadDatabase"`.
- **A dependency is a package of the project** if the project has one by
  that name, and otherwise a package of the registry, at the version in the
  project's lock file. A manifest holds no versions and no paths to other
  packages.
- **A dependency the package never uses is a compile error,** as an unused
  `use` is. A package uses a dependency by naming one of its modules, or by
  calling a method of one of its traits with a dot.
- **`usize_bits = 64`** in `[package]` says that the package runs only on
  64-bit targets. Its code may then rely on `USize` and `ISize` having 64
  bits, it cannot be built for a 32-bit target, and only packages that say
  the same can depend on it. Otherwise the package is verified for both
  widths.
- **A manifest is TOML, read strictly.** A table or a key that is not
  described here is an error, and so is a version.

The standard library is in no manifest: every package may use it, and it
needs no grant.

### Grants

A dependency can use only the capabilities its entry grants. An empty list
grants none, so the package can only do pure computation.

- **Every dependency has a grant,** a project's own packages included, and a
  package needs a grant even for a capability it defines itself.
- **Grants are checked at signatures, wherever a dependency's code is
  named.** A call of a dependency's function is checked against the
  dependency's grant, from the callee's `uses`, and so is every other way of
  using its code: taking its function as a value, using its `impl` where a
  bound or an `any` needs one, and a `provide` of its type. The build fails
  where code names something of a dependency that uses a capability the
  dependency was not granted, and the error names the function and the
  capability.
- **A missing grant is never added by a tool.** `truss check --fix` never
  widens a grant.
- **Running a caller's callback does not count.** A function that runs a
  callback with a `capability Granted` parameter uses no capability of its
  own by doing so.
- Nothing in a package runs when it is fetched or built: there are no build
  scripts, and the code that runs while compiling is pure.

## Projects

A manifest with a `[project]` table makes its directory a project: every
package under it is one of the project's, except those under a directory
whose manifest has a `[project]` table of its own. A package with no such
manifest above it is a project by itself.

```toml
[project]

[test]
time_limit = 10
```

- The project's manifest may also hold a `[package]`, when the project's
  root is itself a package.
- `time_limit` is the time each test of the project may take, in seconds. It
  is 10 unless the manifest says otherwise.
- Two packages of a project cannot have the same name.
- A project's package takes the place of the registry's package of the same
  name, for every package of the build.
- A project's own packages have no versions.

## The lock file

`truss.lock`, beside the project's manifest, holds the version and content of
every registry package the project's packages use, their dependencies' and
their dependencies' in turn. `truss add` and `truss upgrade` write it. It is
kept in version control.

```text
format 1
acme::geometry_v2 2.1.3 6f1c2f0f8f0b7a1e3d9c4a5b6e7d8c9f0a1b2c3d4e5f60718293a4b5c6d7e8f9
truss::postgres 1.12.0 0d4e8a1b7c3f2e6d5a9b8c7f1e0d3a2b4c6e8f0a1c3e5a7b9d1f3e5c7a9b0d2f holds Clock, Handles, NetworkClient
```

- The first line names the format. Each line after it is one package: its
  name, its version, the hash of its content, and after `holds`, the
  capabilities it holds, which are those its users in the build grant it.
  The lines are in order of name.
- A version is three numbers. The first is the number after `_v` at the end
  of the package's name, or 1 for a name without one.
- The hash is of the package's files as the registry holds them. It is the
  BLAKE3 hash of a line for each file, in the order of the bytes of their
  paths: the path, a space, the BLAKE3 hash of the file's bytes as 64
  hexadecimal digits, and a line feed. It is written as 64 hexadecimal
  digits too.
- A lock file that does not match the project's manifests is a compile
  error: a dependency with no line, a line no package uses, or a `holds`
  that the manifests' grants do not give. `truss check --fix` removes a
  line that is not used and corrects a `holds`, and `truss add` adds a
  line.
- A build fetches any locked package it does not have, and uses nothing
  whose hash differs.
- Two changes to a lock file merge by taking the higher version of each
  package.

A published package holds its `truss.toml`, its modules, the Markdown files
beside them, and a `truss.lock` with a line for each registry package it
was published with, without `holds`: those its code uses, its tests apart,
and those that they use in turn. This lock file is the package's *record*.

## Choosing versions

- **A build holds one version of each package.**
- **The version of a package in a build is the highest version that the
  project's lock file or the record of any package of the build names.**
  Nothing newer enters a build until `truss upgrade` or `truss add` writes
  it into the lock file.
- There are no version ranges and no solver.

## Versions

Every release under one name is compatible with the releases before it. A
change that is not compatible is published under a new name, the old one
with `_v2` after it, as in `acme::geometry_v2`. `acme::geometry` and
`acme::geometry_v2` are two packages, and both can be in one build.

The registry checks compatibility from the signatures. A release is
compatible with the one before when:

- every public definition is still there, at the same path
- a function, method, or theorem has the same parameters and result, no
  capability more in its `uses`, a `requires` that the old one implies, an
  `ensures` that implies the old one, and no cost greater than before
- a type that shows its fields has the same fields, variants, and invariant;
  an opaque type may change everything inside it
- a trait or capability has the same methods, associated types, required
  traits, and laws, and gains at most methods that have bodies
- every `impl` is still there
- a constant has the same type and value
- a package that ran on every target still does

Bodies are not promised: a release may change a function's results within
its contract, including a body that the prover reads as a definition and a
parameter's default.

The registry numbers each release. The first is `N.0.0`, where `N` is the
number after `_v` in the package's name, or 1. After that, a release whose
public signatures are unchanged gets the next patch number, and one that
added to them gets the next minor number. There are no 0.x versions.

## The registry

- **A package is published as its source:** its manifest, its modules, its
  lock file, and the Markdown files beside them. Nothing built or generated
  is published.
- **A package is published only when it is finished:** it has no
  diagnostics, every proof is done, it has no `todo` and no `echo`, its
  tests that have no `uses` pass, and every dependency is a registry
  package. The registry checks all of this again itself.
- **The registry keeps an append-only log of every version's hash,** and the
  toolchain checks that each hash it puts in a lock file is in the log.
- **The registry signs the proofs and test results it computed for a
  release.** Each result is keyed by its inputs, so a build uses a signed
  result in place of computing it. The toolchain trusts the registry's key
  unless a project says otherwise.
- **A release can be marked as one not to use,** by its owner or the
  registry, with the reason. Builds that use it still build. `truss upgrade`
  never chooses a marked release, and says when a project is on one.
- A dependency's external tests are never run by a project that depends on
  it.
