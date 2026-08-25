#!/usr/bin/env perl

use strict;
use warnings;

while (<>) {
  s{Source: '[^']*/source/crates/}{Source: 'crates/}g;
  if (/^import Aeneas$/) {
    print "import Aeneas.Std\n";
    print "import Aeneas.Tactic.RustAttributes\n";
    next;
  }
  s/V7Tag73ChallengeQm31Full\./V7Tag73ChallengeQm31\./g;
  print;
}
