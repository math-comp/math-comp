#!/bin/sh

printf "PR number? "
read -r PR

printf "Category? (type a prefix, launch script multiple times if multiple categories)\n"
(cd doc/changelog && ls -d */)
read -r where

where="doc/changelog/$where"
if ! [ -d "$where" ]; then where=$(echo "$where"*); fi
where="$where/$PR-$(git rev-parse --abbrev-ref HEAD | tr / -).md"

printf "File?\n"
read -r in_file

printf "Fixes? (space separated list of bug numbers)\n"
read -r fixes_list

fixes_string="$(echo $fixes_list | sed 's/ /~    and /g; s,\([0-9][0-9]*\),[#\1](https://github.com/math-comp/math-comp/issues/\1),g' | tr '~' '\n')"
if [ ! -z "$fixes_string" ]; then fixes_string="$(printf ',\n    fixes %s' "$fixes_string")"; fi

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
# use %s for the leading - to avoid looking like an option (not sure
# if necessary but doesn't hurt)
printf '%s in `%s`\n  + Describe your change here but do not end with a period\n    for instance: lemmas `lem1`, `lem2` and `lem3`\n    ([#%s](https://github.com/math-comp/math-comp/pull/%s)%s).\n' - "$in_file" "$PR" "$PR" "$fixes_string" > "$where"

printf 'Name of created changelog file:\n'
printf '%s\n' "$where"

giteditor=$(git config core.editor)
if [ "$giteditor" ]; then
    $giteditor "$where"
elif [ "$EDITOR" ]; then
    $EDITOR "$where"
else
    printf "Describe the changes in the above file\n"
fi
