#!/usr/bin/env perl

use strict;
use warnings;
use JSON::PP;

@ARGV == 2 or die "usage: compare-canonical-json.pl LEFT RIGHT\n";

my $codec = JSON::PP->new->max_depth(100_000)->canonical(1)->ascii(1);
my $limit = $ENV{MAX_DIFFS} // 200;
$limit =~ /^\d+\z/ or die "MAX_DIFFS must be a natural number\n";

sub read_json {
  my ($path) = @_;
  local $/;
  open my $input, '<', $path or die "cannot open $path: $!\n";
  my $value = $codec->decode(<$input>);
  close $input or die "cannot close $path: $!\n";
  return $value;
}

sub pointer_key {
  my ($key) = @_;
  $key =~ s/~/~0/g;
  $key =~ s{/}{~1}g;
  return $key;
}

my $differences = 0;

sub report_difference {
  my ($path, $kind, $left, $right) = @_;
  $differences++;
  return if $differences > $limit;
  print "$path\t$kind\t$left\t$right\n";
}

sub encoded {
  my ($value) = @_;
  return $codec->encode($value);
}

sub compare_values {
  my ($left, $right, $path) = @_;
  my $left_ref = ref($left);
  my $right_ref = ref($right);
  if ($left_ref ne $right_ref) {
    report_difference($path, 'type', encoded($left), encoded($right));
    return;
  }
  if ($left_ref eq 'HASH') {
    my %keys = map { $_ => 1 } (keys %$left, keys %$right);
    for my $key (sort keys %keys) {
      my $next = $path . '/' . pointer_key($key);
      if (!exists $left->{$key}) {
        report_difference($next, 'missing-left', '<missing>',
          encoded($right->{$key}));
      } elsif (!exists $right->{$key}) {
        report_difference($next, 'missing-right', encoded($left->{$key}),
          '<missing>');
      } else {
        compare_values($left->{$key}, $right->{$key}, $next);
      }
    }
    return;
  }
  if ($left_ref eq 'ARRAY') {
    if (@$left != @$right) {
      report_difference($path, 'array-length', scalar(@$left), scalar(@$right));
    }
    my $common = @$left < @$right ? @$left : @$right;
    for my $index (0 .. $common - 1) {
      compare_values($left->[$index], $right->[$index], "$path/$index");
    }
    return;
  }
  my $left_encoded = encoded($left);
  my $right_encoded = encoded($right);
  if ($left_encoded ne $right_encoded) {
    report_difference($path, 'value', $left_encoded, $right_encoded);
  }
}

compare_values(read_json($ARGV[0]), read_json($ARGV[1]), '');
if ($differences == 0) {
  print "canonical JSON documents are identical\n";
  exit 0;
}
print "differences: $differences";
print " (first $limit shown)" if $differences > $limit;
print "\n";
exit 1;
