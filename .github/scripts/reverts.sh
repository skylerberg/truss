#!/bin/sh
# Fails when a pull request takes out one of the last merges into main: it
# changes every file that merge changed, and puts one of them back to what
# it was before the merge. A commit made from an older tree on top of a
# newer main does that to every merge the older tree lacks, with no
# conflict. It reads the pull request's merge commit, which is the one
# checked out unless another is named.
set -eu

merge=${1:-HEAD}
base=$(git rev-parse "$merge^1")
changed=$(git diff --name-only "$base" "$merge")

found=0
for merged in $(git rev-list --first-parent -n 30 "$base"); do
  before=$(git rev-parse -q --verify "$merged^1") || break
  files=$(git diff --name-only "$before" "$merged")
  [ -n "$files" ] || continue

  every=1
  for file in $files; do
    if ! printf '%s\n' "$changed" | grep -qxF -- "$file"; then
      every=0
      break
    fi
  done
  [ "$every" = 1 ] || continue

  for file in $files; do
    now=$(git rev-parse -q --verify "$merge:$file" || echo none)
    was=$(git rev-parse -q --verify "$before:$file" || echo none)
    if [ "$now" = "$was" ]; then
      echo "$(git log -1 --format='%h %s' "$merged") is taken out: $file is back to what it was before it."
      found=1
      break
    fi
  done
done

if [ "$found" = 1 ]; then
  echo
  echo "If the branch was squashed onto a main that had moved, go back to the"
  echo "branch as it was before the squash, merge main into it, and squash"
  echo "again. A pull request that means to take a merge out says so: its"
  echo "title starts with \"Revert\"."
fi
exit "$found"
