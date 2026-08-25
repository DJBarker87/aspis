#!/usr/bin/env perl

use strict;
use warnings;

@ARGV == 2 or die
  "usage: assert-accepted-source-axioms.pl BRIDGE_LOG GREEN_SAMPLER_LOG\n";

sub read_text {
  my ($path) = @_;
  local $/;
  open my $input, '<', $path or die "cannot open $path: $!\n";
  my $text = <$input>;
  close $input or die "cannot close $path: $!\n";
  return $text;
}

sub theorem_axioms {
  my ($text, $name, $path) = @_;
  if ($text =~ /'\Q$name\E' does not depend on any axioms/) {
    return ();
  }
  $text =~ /'\Q$name\E' depends on axioms:\s*\[([^\]]*)\]/s
    or die "missing #print axioms result for $name in $path\n";
  my @axioms = split /,/, $1;
  for my $axiom (@axioms) {
    $axiom =~ s/^\s+|\s+$//g;
    length($axiom) or die "empty axiom name for $name in $path\n";
  }
  return @axioms;
}

my $bridge_log = read_text($ARGV[0]);
my $sampler_log = read_text($ARGV[1]);
my %allowed = map { $_ => 1 } qw(propext Classical.choice Quot.sound);

my @checks = (
  [ $bridge_log, $ARGV[0],
    'V7CompactSemanticSourceBridge.accepted_execution_prefix_eta_eq' ],
  [ $bridge_log, $ARGV[0],
    'V7CompactSemanticSourceBridge.accepted_main_exposes_exact_outer_trace' ],
  [ $bridge_log, $ARGV[0],
    'V7CompactSemanticSourceBridge.accepted_main_exposes_exact_prefix_eta' ],
  [ $sampler_log, $ARGV[1],
    'V7CompactSemanticFullGenerated.transcript.Transcript.challenge_qm31_is_source_generated' ],
);

for my $check (@checks) {
  my ($text, $path, $name) = @$check;
  my @axioms = theorem_axioms($text, $name, $path);
  my %seen;
  for my $axiom (@axioms) {
    $allowed{$axiom}
      or die "non-standard axiom $axiom in $name\n";
    !$seen{$axiom}++
      or die "duplicate axiom $axiom in $name\n";
  }
  print "$name axioms: [", join(', ', @axioms), "]\n";
}

$sampler_log =~ /V7 Tag-73 challenge_qm31 source replay: PASS/
  or die "green sampler replay marker missing in $ARGV[1]\n";
$sampler_log =~ /canonical LLBC sha256:\s*0c9f44a7a426b7efd1404e8776795958d89f203eca2915994d013a756b27d857/
  or die "canonical sampler LLBC digest missing in $ARGV[1]\n";

print "accepted-source callback axiom: absent\n";
print "sampler replacement certificate: standard Lean axioms only\n";
