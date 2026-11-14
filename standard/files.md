# standard::files

Functions on files built from the `FileRead`, `FileWrite`, and `Handles`
capabilities, and the implementations of those capabilities for tests and
for narrowing.

## Writing

A buffered writer is only lent, inside a scope. `write_with` lends the
writer to a function, then writes out the remaining buffered data, and
returns the first error, from the function or from writing:

```truss
fn save_report(path: Path, report: Report) -> Result[Unit, SystemError]
  uses FileWrite, Handles
{
  files::write_with(path, write: fn(writer) {
    mut writer.write(report.header())?
    mut writer.write(report.body())
  })
}
```

Code never owns a writer, so no writer is dropped with data in it. A type
that writes in stages takes the writer as a `mut` parameter of each call.

## Temporary files

`with_temporary_directory(work)` creates a directory under
`temporary_root()`, runs `work` with its path, and removes the directory and
everything in it afterwards. `with_temporary_file(work)` does the same with
an empty file inside such a directory. `temporary_root()` is `$TMPDIR`, or
`/tmp` when it is not set.

## Implementations

- `MemoryFiles` is an in-memory file system, with directories, links,
  permissions, and open files, which returns the error the operating system
  returns for each misuse. `MemoryFiles.new().with_text(path, contents: text)`
  adds a file.
- `FilesWithin(root:)` narrows `FileRead` to the files under `root`: each
  path is joined to `root`, and a path that leaves it, such as
  `../secrets`, fails with a `SystemError`.

```truss
type FilesWithin(root: Path)

impl FileRead for FilesWithin
  uses FileRead
{
  fn read(self, file: Path) -> Result[List[UInt8], SystemError] {
    FileRead.read(self.root.join_confined(file)?)
  }
}

let summary = provide files::FilesWithin(root: Path.new("logs")) {
  log_report::summarize(Path.new("access.log"))
}
```

The `impl` shows one of `FileRead`'s methods; the rest are written the same
way.
