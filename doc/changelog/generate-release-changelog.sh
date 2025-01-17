#!/usr/bin/env bash

OUT=CHANGELOG_UNRELEASED.md

echo "Add the lines below to CHANGELOG.md" > ${OUT}
echo "" >> ${OUT}

changelog_entries_with_title=(doc/changelog/*/*.md)
for f in "${changelog_entries_with_title[@]}"; do
    cat ${f} >> ${OUT}
    echo "" >> ${OUT}
done

echo "Output written in ${OUT}"
