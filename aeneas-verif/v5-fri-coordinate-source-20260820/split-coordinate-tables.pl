#!/usr/bin/env perl
use strict;
use warnings;

# Deterministically turn the two very large dependent Array literals emitted
# by Aeneas into 16-entry declarations.  The entry text and order are copied
# verbatim.  This avoids quadratic elaborator memory in the default
# `Array.make` length proof while preserving the represented arrays exactly.

my ($combined, $high_out, $low_out) = @ARGV;
die "usage: $0 FunsCombined.lean FunsHighWindow.lean FunsLowWindow.lean\n"
  unless defined $low_out;

open my $input, '<', $combined or die "open $combined: $!\n";
local $/;
my $source = <$input>;
close $input;

sub module_header {
  my ($import) = @_;
  return <<"HEADER";
-- Deterministic low-memory normalization of the recorded Aeneas output.
import $import
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace V5FriCoordinateAdapter

HEADER
}

sub write_table_module {
  my (%args) = @_;
  my $start = quotemeta($args{start_marker});
  my $end = quotemeta($args{end_marker});
  $source =~ /($start.*?)(?=$end)/s
    or die "could not find $args{name} block\n";
  my $block = $1;
  my @entries = ($block =~
    /(Array\.make 2#usize \[ \d+#u32, \d+#u32 \]|\ba\b(?=\s*,))/g);
  @entries = map {
    $_ eq 'a'
      ? 'Array.make 2#usize [ 2147450879#u32, 2147450879#u32 ]'
      : $_
  } @entries;
  die "$args{name}: expected $args{count} entries, got " . scalar(@entries) . "\n"
    unless @entries == $args{count};

  open my $output, '>', $args{output} or die "open $args{output}: $!\n";
  print {$output} module_header($args{import});

  my $chunks = $args{count} / 16;
  for my $chunk (0 .. $chunks - 1) {
    print {$output} "private def $args{prefix}Chunk$chunk :\n";
    print {$output} "    Array (Array Std.U32 2#usize) 16#usize :=\n";
    print {$output} "  Array.make 16#usize [\n";
    for my $offset (0 .. 15) {
      my $entry = $entries[$chunk * 16 + $offset];
      my $comma = $offset == 15 ? '' : ',';
      print {$output} "    $entry$comma\n";
    }
    print {$output} "  ] (by rfl)\n\n";
  }

  print {$output} "/-- Exact normalized declaration of the Aeneas literal table. -/\n";
  print {$output} "@[global_simps, rust_const \"$args{rust_name}\"]\n";
  print {$output} "def $args{lean_name}\n";
  print {$output} "  : Array (Array Std.U32 2#usize) $args{count}#usize :=\n";
  print {$output} "  Array.make $args{count}#usize (\n";
  for my $chunk (0 .. $chunks - 1) {
    my $suffix = $chunk == $chunks - 1 ? '' : ' ++';
    print {$output} "    $args{prefix}Chunk$chunk.val$suffix\n";
  }
  print {$output} "  ) (by\n";
  print {$output} "    simp only [List.length_append, Array.length_eq]\n";
  print {$output} "    norm_num)\n\n";
  print {$output} "end V5FriCoordinateAdapter\n";
  close $output;
}

write_table_module(
  output => $high_out,
  import => 'Coordinates.FunsField',
  start_marker => '/-- [aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW]',
  end_marker => '/-- [aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW]',
  name => 'high window', count => 512, prefix => 'rate512High',
  rust_name => 'aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW',
  lean_name => 'aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW',
);

write_table_module(
  output => $low_out,
  import => 'Coordinates.FunsHighWindow',
  start_marker => '/-- [aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW]',
  end_marker => '/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]: loop body 0:',
  name => 'low window', count => 256, prefix => 'rate512Low',
  rust_name => 'aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW',
  lean_name => 'aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW',
);
