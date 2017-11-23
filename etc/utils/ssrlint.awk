#! /usr/bin/gawk -f

# USAGE> $(git root)/etc/utils/ssrlint.awk file1.v file2.v ...
#
# This script should be called with an ssr .v file as argument
# It will check for the following style mistakes:
# - checking that lines are less than 79 characters long
# - checking that indentation is formed by an even number of spaces
# - checking for terminators in one line proofs
# - /!\ "indentation for subgoal" checking is not implemented yet

#@include "inplace"

# BEGIN {RS = "\n"}
# line counter
{fileline[FILENAME]++}
{line = fileline[FILENAME]}

# Proof management
{inlineproof = 0}
/^Proof.*Qed/ {inlineproof=1}
/^Proof.$/ {proof = 1
            subgoals = 1}
!proof &&  /^Qed.$/  \
  {print "Qed outside of a proof in file " FILENAME " at line " line > "/dev/stderr"}
proof && /^Qed.$/    {proof = 0}

# Proof indentation management
proof && /^(  )+[^ ]/ {}

# Checking for missing terminators in one line proofs
/^Proof\\..*Qed./ {wrongonelineproof = 1}
/^Proof\\. (by|exact|done).*Qed/ {wrongonelineproof = 0}
wrongonelineproof {\
  print "missing terminators in file " FILENAME " at line " line \
   > "/dev/stderr"}

# Checking for missing terminatores in multiple line proofs
# (subgoals > 0) && /Qed/ {print "missing terminators in file " FILENAME " at line " line \
#         > "/dev/stderr"}
# expectqed && ! /^(by|exact|done)/ \
#   {print "expecting Qed at " line > "/dev/stderr"}

# Checking that indentation is even
proof && /^(  )+ [^ ]/ {\
  print "identation is not even in proof in file " FILENAME " at line " line > "/dev/stderr"}

# Checking for lines that are too long
       {if (length($0) > 80) \
        print "line is too long (" length($0) "> 80) in file " FILENAME " at line " line \
        > "/dev/stderr"}
/^Qed.$/    {subgoals = 0}

# Multiple moves on the same line
/(move|case).*(move)/ {\
        print "multiple move/case in the same line in file " FILENAME " at line " line \
        > "/dev/stderr"}

# Rewriting
#!proof  {print $0}
      # { print "Record =", $0,"and RT = [" RT "]" }
