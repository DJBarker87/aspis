#!/usr/bin/env perl

use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use JSON::PP;

@ARGV == 2 or die
  "usage: assert-mir-only-drift.pl BUNDLED_CANONICAL REPLAYED_CANONICAL\n";

my $codec = JSON::PP->new
  ->max_depth(100_000)
  ->canonical(1)
  ->ascii(1);

sub read_json {
  my ($path) = @_;
  local $/;
  open my $input, '<', $path or die "cannot open $path: $!\n";
  my $value = $codec->decode(<$input>);
  close $input or die "cannot close $path: $!\n";
  return $value;
}

sub mir_slot {
  my ($document, $path) = @_;
  ref($document) eq 'HASH' && ref($document->{translated}) eq 'HASH' &&
      ref($document->{translated}{options}) eq 'HASH' &&
      exists $document->{translated}{options}{mir}
    or die "missing /translated/options/mir in $path\n";
  return \$document->{translated}{options}{mir};
}

my $bundled = read_json($ARGV[0]);
my $replayed = read_json($ARGV[1]);
my $bundled_mir = mir_slot($bundled, $ARGV[0]);
my $replayed_mir = mir_slot($replayed, $ARGV[1]);

!defined($$bundled_mir)
  or die "expected bundled /translated/options/mir = null\n";
defined($$replayed_mir) && !ref($$replayed_mir) && $$replayed_mir eq 'Built'
  or die "expected replayed /translated/options/mir = \"Built\"\n";

# Erase exactly the whitelisted invocation spelling and demand byte equality
# of the already path/destination/order-normalized structured documents.
$$replayed_mir = undef;
my $bundled_bytes = $codec->encode($bundled);
my $replayed_bytes = $codec->encode($replayed);
$bundled_bytes eq $replayed_bytes
  or die "structured LLBC drift exists outside /translated/options/mir\n";

print "bundled /translated/options/mir: null\n";
print "replayed /translated/options/mir: \"Built\"\n";
print "remaining structured LLBC tree: byte-equal\n";
print "normalized structured LLBC sha256: ", sha256_hex($bundled_bytes), "\n";
