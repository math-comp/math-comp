#!/bin/zsh

COQFINITGROUP=$1

for f in $COQFINITGROUP/theories/*.v
  do nf=$(find . -name $(basename $f))
  echo "copy $f to $nf"
  cp $f $nf
done
for f in $COQFINITGROUP/ssreflect/test/*.v
  do nf=$(find . -name $(basename $f))
  echo "copy $f to $nf"
  cp $f $nf
done
sed "s/Require Import ssrmatching\./Require Import mathcomp.ssreflect.ssrmatching./" -i */*.v
sed "s/Require ssreflect\./Require mathcomp.ssreflect.ssreflect./" -i */*.v
sed "s/Require Import ssreflect/Require Import mathcomp.ssreflect.ssreflect.\nRequire Import/" -i */*.v
sed "s/Require Import/From mathcomp Require Import/" -i */*.v
sed "s/From mathcomp Require Import mathcomp/Require Import mathcomp/" -i */*.v
sed "s/From mathcomp Require Import BinNat/Require Import BinNat/" -i */*.v
sed "s/From mathcomp Require Import Arith/Require Import Arith/" -i */*.v
sed "s/From mathcomp Require Import Bool/Require Import Bool/" -i */*.v
sed "s/From mathcomp Require Import\.//" -i */*.v
sed "s/From mathcomp Require Import/From mathcomp\nRequire Import/" -i */*.v
