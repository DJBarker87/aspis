#!/usr/bin/env perl

use strict;
use warnings;
use JSON::PP;

my $preserve_mir = 0;
if (@ARGV == 2 && $ARGV[0] eq '--preserve-mir') {
  $preserve_mir = 1;
  shift @ARGV;
}
@ARGV == 1 or die
  "usage: canonicalize-llbc.pl [--preserve-mir] FILE.llbc\n";

my $codec = JSON::PP->new
  ->max_depth(100_000)
  ->canonical(1)
  ->ascii(1);

local $/;
open my $input, '<', $ARGV[0]
  or die "cannot open $ARGV[0]: $!\n";
my $document = $codec->decode(<$input>);
close $input or die "cannot close $ARGV[0]: $!\n";

my $translated = $document->{translated};
ref($translated) eq 'HASH'
  or die "missing translated object in $ARGV[0]\n";
ref($translated->{options}) eq 'HASH'
  or die "missing translated.options object in $ARGV[0]\n";

$translated->{options}{dest_dir} = undef;
$translated->{options}{dest_file} = undef;

# `cargo --mir built` and Charon's default built-MIR selection serialize as
# `"Built"` and `null`, respectively, while producing the same translated
# tree.  The replay separately proves that this is the sole pre-normalization
# difference.  Reject every other value before erasing this invocation-only
# spelling distinction.
exists $translated->{options}{mir}
  or die "missing translated.options.mir in $ARGV[0]\n";
if (!$preserve_mir) {
  my $mir = $translated->{options}{mir};
  (!defined($mir) || (!ref($mir) && $mir eq 'Built'))
    or die "unexpected translated.options.mir in $ARGV[0]\n";
  $translated->{options}{mir} = undef;
}

# Charon records absolute paths for dependency sources outside the tiny
# extraction harness.  The deployed files are checked independently by
# DEPLOYED-SOURCE.sha256, so normalize only that pinned aspis-core prefix and
# keep every path below it intact.  Rust sysroot paths and the harness-local
# `src/lib.rs` remain untouched.
my $files = $translated->{files};
ref($files) eq 'ARRAY'
  or die "missing translated.files array in $ARGV[0]\n";
for my $file (@$files) {
  ref($file) eq 'HASH' && ref($file->{name}) eq 'HASH'
    or die "malformed translated.files entry in $ARGV[0]\n";
  next unless exists $file->{name}{Local};
  my $path = $file->{name}{Local};
  if ($path =~ m{(?:^|/)source/(crates/aspis-core/.*)\z}) {
    $file->{name}{Local} = $1;
  }
}

for my $name (qw(item_names short_names)) {
  my $entries = $translated->{$name};
  ref($entries) eq 'ARRAY'
    or die "missing translated.$name array in $ARGV[0]\n";
  my @keyed = map {
    ref($_) eq 'HASH' && exists $_->{key}
      or die "malformed translated.$name entry in $ARGV[0]\n";
    [ $codec->encode($_->{key}), $codec->encode($_), $_ ]
  } @$entries;
  @keyed = sort {
    $a->[0] cmp $b->[0] || $a->[1] cmp $b->[1]
  } @keyed;
  $translated->{$name} = [ map { $_->[2] } @keyed ];
}

print $codec->encode($document);
