#!/usr/bin/env bash
set -e
shopt -s nullglob

if [ "$DEBUG" = 1 ]; then
  set -x
fi

show_help(){
    cat <<EOF
Usage: changes [-h|-?|--help]        // prints this
               [[-s|--since] Commit] // compares to Commit
               [-r|--raw]            // show raw data from the db
               [--pp]                // pretty print raw data from the db
               [--cd]                // cd to the tmp dir where the raw data is
               [-i|--interactive]    // run sqllite on the db
               [-e|--exclude]        // excludes a list of names
               [-c|--check]          // checks that a changelog contains all the changes
               file*
EOF
}

die() {
    printf '%s\n' "$1" >&2
    exit 1
}

while :; do
    case $1 in
        -h|-\?|--help)
            show_help    # Display a usage synopsis.
            exit 0
            ;;
        -s|--since)
            shift
            COMMIT=$1
            shift
            ;;
        -c|--check)
            shift
            CHANGELOG=$1
            OUTMODE="check"
            shift
            ;;
        -e|--exclude)
            shift
            EXCLUDE=$1
            shift
            ;;
        -r|--raw)
            OUTMODE="raw"
            shift
            ;;
        --pp)
            OUTMODE="pp"
            shift
            ;;
        --cd)
            CD=1
            shift
            ;;
        -i|--interactive)
            INTERACTIVE=1
            shift
            ;;
        *)
            if ! [ "$*" ]; then break
            else FILES=$*; break
            fi
            ;;

    esac
done

if ! [ "$OUTMODE" ]; then OUTMODE="changelog"; fi
if ! [ "$FILES" ]; then FILES=**/*.v; fi
if ! [ "$COMMIT" ]; then COMMIT="master"; fi
if ! [ "$EXCLUDE" ]; then EXCLUDE=$(mktemp); touch $EXCLUDE; fi

if ! [ -f "$EXCLUDE" ]; then
  echo "$EXCLUDE does not exist"
  exit 1
fi

D=$(mktemp -d)
DB=$D/changes.db
if [ "$OUTMODE" == "pp" ]; then echo "Contents of $DB"; fi

SQL="sqlite3 --line $DB -column -noheader -list -nullvalue NULL"
SQLPP="sqlite3 --line $DB -column -header -nullvalue NULL"
$SQL 'create table changes (name, class, added_file, removed_file, deprecated_file, deprecated_note, line INTEGER);'
$SQL 'create unique index changes_idx on changes(name);'

VERNAC="Definition Notation Lemma Theorem Corollary"
ALLV=$(echo $VERNAC | sed "s/ /_/g")

touchp() { mkdir -p "$(dirname "$1")" && touch "$1" ; }

len() { wc -l $1 | cut -d" " -f 1; }

INDENT=4
MAXLENGTH=80

sql() {
  OUT=$(mktemp);
  $SQL "$*" > $OUT
  RAW=$(cat $OUT)
  LEN=$(len $OUT)
  PP=$(cat $OUT | awk -F "|" -v LEN=$LEN -v INDENT=$INDENT -v INIT=$INIT -v MAXLENGTH=$MAXLENGTH '
        function println(s, off) {
          l = length(s)
          if (OUTLEN + l + off <= MAXLENGTH) printf s
          else {
            OUTLEN = INDENT
            printf "\n"
            for (j = 0; j < INDENT; j++) { printf " " }
            printf s
          }
          OUTLEN += l
        }

        BEGIN { OUTLEN = INIT }
        (NR == LEN && LEN > 1) { println("and ") }
        { println(sprintf("`%s`", $1), 2)
          if ($2) println(sprintf(" (%s)", $2), 2) }
        (NR < LEN && LEN > 1) { println(", ", -2) }
        (NR == LEN) { printf ".\n" }' ORS=" ")
}

class() {
  if [ $1 == 1 ]; then
      echo $2 | sed "s/Definition/definition/;s/Notation/notation/;
      s/Lemma/lemma/;s/Theorem/theorem/;s/Corollary/corollary/;"
  else
      echo $2 | sed "s/Definition/definitions/;s/Notation/notations/;
      s/Lemma/lemmas/;s/Theorem/theorems/;s/Corollary/corollaries/;"
  fi
}

for f in $FILES; do
  touchp $D/diffs/$f
  git diff "$COMMIT" -- $f > $D/diffs/$f
done

for f in $FILES; do
  cat $D/diffs/$f | awk -f etc/changes.awk -v file=$f | $SQL --batch
done

$SQL "select name from changes" > $D/all_changes

cat $EXCLUDE | while read d; do
  $SQL "delete from changes where name = \"$d\";"
done

$SQL "select name from changes" > $D/nonexcluded_changes

$SQL 'create table deprecated (name, file, renamed INTEGER, generalized INTEGER, target, target_file, note);'
$SQL 'create unique index deprecated_idx on deprecated(name);'

parse_deprecated() {
  NAME=$1
  shift
  FILE=$1
  shift
  RENAMED=0
  GENERALIZED=0
  TARGET=$(echo $* | grep -Fo -f $D/all_changes || true)
  if [ "$TARGET" ]; then
    if echo $* | grep -qo "rename"; then RENAMED=1; fi
    if echo $* | grep -qEo "generali[zs]e"; then GENERALIZED=1; fi
    TARGET_FILE=$($SQL "select added_file from changes where name=\"$TARGET\";")
  fi
  $SQL "insert into deprecated values
     (\"$NAME\", \"$FILE\", $RENAMED, $GENERALIZED, \"$TARGET\", \"$TARGET_FILE\", \"$*\");"
  $SQL "delete from changes where name=\"$NAME\";"
  if [ "$RENAMED" == "1" ] || [ "$GENERALIZED" == "1" ]; then
    $SQL "delete from changes where name=\"$TARGET\";"
  fi
}

$SQL "select name, deprecated_file, deprecated_note from changes
      where deprecated_file != \"\"" |\
while read d; do
  args=${d//|/ }
  parse_deprecated $args
done

case $OUTMODE in
  "raw")
    echo "=========================================="
    $SQL "select * from changes;"
    echo "=========================================="
    ;;
  "pp")
    echo "=========================================="
    $SQLPP "select * from changes;"
    echo "=========================================="
    ;;
  "changelog")
    echo "### Added"
    echo ""
    for f in $FILES; do
      sql "select name from changes where removed_file=\"\"
           and added_file=\"$f\" and deprecated_file=\"\";"
      if [ $LEN -gt 0 ]; then
        echo "- in file \`$(basename $f)\`,"
        for v in $VERNAC; do
          INIT=20
          sql "select name from changes where removed_file=\"\"
               and added_file=\"$f\" and class=\"$v\";"
          if [ $LEN -gt 0 ]; then
            echo "  + new $(class $LEN $v) $PP"
          fi
        done
      fi
    done
    echo ""
    echo "### Renamed"
    echo ""
    for f in $FILES; do
      INIT=20
      sql "select name, target from deprecated
           where renamed = 1 and generalized = 0
           and target_file = \"$f\" and file = \"$f\";"
      if [ $LEN -gt 0 ]; then
        echo "- in file \`$(basename $f)\`,"
        cat $OUT | sed "s/^\(.*\)|\(.*\)/  + \`\1\` -> \`\2\`/"
      fi
      sql "select distinct file from deprecated
           where renamed = 1 and generalized = 0
           and target_file = \"$f\" and file != \"$f\";"
      if [ $LEN -gt 0 ]; then
        SRCS=$RAW
        for s in $SRCS; do
          INIT=50
          sql "select name, target from deprecated
               where renamed = 1 and generalized = 0
               and target_file = \"$f\" and file = \"$s\";"
          echo "- moved from \`$(basename $s)\` to \`$(basename $f)\`:"
          cat $OUT | sed "s/^\(.*\)|\(.*\)/  + \`\1\` -> \`\2\`/"
        done
      fi
    done
    echo ""
    echo "### Generalized"
    echo ""
    for f in $FILES; do
      INIT=20
      sql "select name, target from deprecated
           where generalized = 1
           and target_file = \"$f\" and file = \"$f\";"
      if [ $LEN -gt 0 ]; then
        echo "- in file \`$(basename $f)\`,"
        cat $OUT | sed "s/^\(.*\)|\(.*\)/  + \`\1\` -> \`\2\`/"
      fi
      sql "select distinct file from deprecated
           where generalized = 1
           and target_file = \"$f\" and file != \"$f\";"
      if [ $LEN -gt 0 ]; then
        SRCS=$RAW
        for s in $SRCS; do
          INIT=50
          sql "select name, target from deprecated
               where generalized = 1
               and target_file = \"$f\" and file = \"$s\";"
          echo "- moved from \`$(basename $s)\` to \`$(basename $f)\`:"
          cat $OUT | sed "s/^\(.*\)|\(.*\)/  + \`\1\` -> \`\2\`/"
        done
      fi
    done
    echo ""
    echo "### Deprecated"
    echo ""
    for f in $FILES; do
      INIT=20
      sql "select name, note from deprecated where file=\"$f\" and renamed = 0 and generalized = 0;"
      if [ $LEN -gt 0 ]; then
       echo "- in file \`$(basename $f)\`, deprecated"
       cat $OUT | sed "s/^\(.*\)|\(.*\)/  + \`\1\` (\2),/"
      fi
    done
    echo ""
    echo "### Maybe changed"
    echo ""
    for f in $FILES; do
      INIT=20
      sql "select name from changes where added_file=\"$f\"
           and removed_file=\"$f\" and deprecated_file=\"\";"
      if [ $LEN -gt 0 ]; then
        echo "- in file \`$(basename $f)\`, updated $PP"
      fi
    done
    echo ""
    echo "### Moved from one file to another and maybe changed or generalized"
    echo ""
    for f in $FILES; do
      sql "select distinct removed_file from changes where added_file=\"$f\"
           and removed_file != \"\" and removed_file != \"$f\"
           and deprecated_file=\"\";"
      if [ $LEN -gt 0 ]; then
        SRCS=$RAW
        for s in $SRCS; do
          INIT=50
          sql "select name from changes where added_file=\"$f\"
               and removed_file=\"$s\" and deprecated_file=\"\";"
          echo "- moved from \`$(basename $s)\` to \`$(basename $f)\`: $PP"
        done
      fi
    done
    echo ""
    echo "### Removed"
    echo ""
    for f in $FILES; do
      INIT=20
      sql "select name from changes where added_file=\"\"
           and removed_file=\"$f\" and deprecated_file=\"\";"
      if [ $LEN -gt 0 ]; then
        echo "- in file \`$(basename $f)\`, removed $PP"
      fi
    done
    ;;
  "check")
    cat $D/nonexcluded_changes | while read d; do
      grep -q "\`$d\`" $CHANGELOG || echo $d
    done > $D/absent_from_changelog
    LEN=$(len $D/absent_from_changelog);
    if [ $LEN -gt 0 ]; then
        cat $D/absent_from_changelog
    fi
    ;;
esac

if [ "$CD" ]; then cd $D; exec $SHELL; fi
if [ "$INTERACTIVE" ]; then rlwrap sqlite3 $DB; fi
