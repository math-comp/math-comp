# Unreleased changelog #

## When to add an entry? ##

All new features, user-visible changes to features, user-visible or
otherwise important infrastructure changes, and important bug fixes
should get a changelog entry.

Compatibility-breaking changes should always get a changelog entry,
which should explain what compatibility breakage is to expect.

## How to add an entry? ##

Run `./doc/changelog/make-entry.sh`: it will ask you for your PR
number, and to choose among the predefined categories. Afterward, fill
in the automatically generated entry with a short description of your
change (which should describe any compatibility issues in particular).
You may also add a reference to the relevant fixed issue, and credit
reviewers, co-authors, and anyone who helped advance the PR.

The format for changelog entries is the same as in the CHANGELOG.md
file.

Here is a summary of the structure of a changelog entry in
`doc/changelog/01-added/`:

``` rst
- in `SomeFile.v`

  + lemmas `lem1`, `lem2` and `lem3`
  (`#PRNUM <https://github.com/math-comp/math-comp/pull/PRNUM>`_,
  [fixes `#ISSUE1 <https://github.com/math-comp/math-comp/issues/ISSUE1>`_
  [ and `#ISSUE2 <https://github.com/math-comp/math-comp/issues/ISSUE2>`_],]
  by Full Name[, with help / review of Full Name]).
```

The first line indicates the affected file. Multiple items can be put
in the same changelog entry if multiple files are affected.
One can take example on the entries already present in `CHANGELOG.md`.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).
