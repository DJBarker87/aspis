#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use File::Path qw(make_path);

my ($input, $output_dir) = @ARGV;
die "usage: $0 <normalized-monolithic-funs> <generated-module-dir>\n"
    unless defined($input) && defined($output_dir);

open my $input_fh, '<', $input or die "open $input: $!\n";
local $/;
my $text = <$input_fh>;
close $input_fh;

my $namespace = 'PoolV1CopyLaneBooleanGenerated';
my ($body) = $text =~
    /^namespace \Q$namespace\E\s*\n(.*)^end \Q$namespace\E\s*$/ms;
die "could not isolate generated namespace body\n" unless defined($body);

my @starts;
while ($body =~ m{^/-- \[}mg) {
    push @starts, $-[0];
}
die "expected 55 generated declaration blocks, found " . scalar(@starts) . "\n"
    unless @starts == 55;

my @source_declarations;
for my $index (0 .. $#starts) {
    my $end = $index == $#starts ? length($body) : $starts[$index + 1];
    my $declaration = substr($body, $starts[$index], $end - $starts[$index]);
    $declaration =~ s/\s+\z/\n/;
    push @source_declarations, $declaration;
}

sub split_pattern_declaration {
    my ($declaration, $source_index) = @_;
    my ($variant) = $declaration =~
        /constants::([A-Z_]+)_COPY_PATTERNS\]/;
    return ({ body => $declaration, label => "$source_index.original" })
        unless defined($variant);

    my $assignment = "\n  :=\n";
    my $assignment_at = index($declaration, $assignment);
    die "missing pattern-table assignment for source block $source_index\n"
        if $assignment_at < 0;
    my $body_at = $assignment_at + length($assignment);
    my $array_marker = "  Array.make 13#usize [";
    my $array_at = index($declaration, $array_marker, $body_at);
    die "missing 13-pattern array for source block $source_index\n"
        if $array_at < 0;
    my $header = substr($declaration, 0, $body_at);
    my $prelude = substr($declaration, $body_at, $array_at - $body_at);
    my $elements_at = $array_at + length($array_marker);

    my ($brackets, $braces, $parens) = (1, 0, 0);
    my $element_at = $elements_at;
    my @elements;
    my $array_end;
    for (my $at = $elements_at; $at < length($declaration); ++$at) {
        my $character = substr($declaration, $at, 1);
        if ($character eq '[') {
            ++$brackets;
        } elsif ($character eq ']') {
            if ($brackets == 1 && $braces == 0 && $parens == 0) {
                push @elements, substr($declaration, $element_at, $at - $element_at);
                $array_end = $at;
                last;
            }
            --$brackets;
        } elsif ($character eq '{') {
            ++$braces;
        } elsif ($character eq '}') {
            --$braces;
        } elsif ($character eq '(') {
            ++$parens;
        } elsif ($character eq ')') {
            --$parens;
        } elsif ($character eq ',' && $brackets == 1 && $braces == 0 &&
                $parens == 0) {
            push @elements, substr($declaration, $element_at, $at - $element_at);
            $element_at = $at + 1;
        }
    }
    die "unterminated pattern array for source block $source_index\n"
        unless defined($array_end);
    for my $element (@elements) {
        $element =~ s/^\s+//;
        $element =~ s/\s+$//;
    }
    die "expected 13 pattern records for $variant, found " . scalar(@elements) . "\n"
        unless @elements == 13;

    my $constant_prefix =
        'pool_v1.payment_semantic_terminal.constants.generated_split.';
    my $pattern_type =
        'pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern';
    my @expanded;
    my %base_names;
    while ($prelude =~ /^  let (a\d*) := (Array\.repeat 16#usize (\d+)#(u8|u32))$/mg) {
        my ($local, $expression, $scalar) = ($1, $2, $4);
        my $helper = $constant_prefix . $variant . '_COPY_PATTERN_BASE_' . $local;
        my $element_type = $scalar eq 'u8' ? 'Std.U8' : 'Std.U32';
        my $helper_declaration =
            "/-- Shared generated base array factored only for bounded elaboration. -/\n" .
            "def $helper : Array $element_type 16#usize :=\n  $expression\n";
        push @expanded,
            { body => $helper_declaration,
              label => "$source_index.base.$local" };
        $base_names{$local} = $helper;
    }
    die "expected 15 shared pattern bases for $variant, found " .
        scalar(keys %base_names) . "\n"
        unless keys(%base_names) == 15;

    my @helper_names;
    for my $entry (0 .. $#elements) {
        my $helper = sprintf('%s%s_COPY_PATTERN_%02d',
            $constant_prefix, $variant, $entry);
        my $element = $elements[$entry];
        for my $local (sort { length($b) <=> length($a) } keys %base_names) {
            $element =~ s/\b\Q$local\E\b/$base_names{$local}/g;
        }
        my $helper_declaration =
            "/-- Declaration-preserving elaboration split for generated " .
            "$variant pattern $entry. -/\n" .
            "def $helper :\n  $pattern_type :=\n" .
            "  " . $element . "\n";
        push @expanded,
            { body => $helper_declaration,
              label => sprintf('%s.helper%02d', $source_index, $entry) };
        push @helper_names, $helper;
    }

    my $rebuilt = $header . "  Array.make 13#usize [\n";
    for my $entry (0 .. $#helper_names) {
        my $comma = $entry == $#helper_names ? '' : ',';
        $rebuilt .= "    $helper_names[$entry]$comma\n";
    }
    $rebuilt .= "    ]\n";
    push @expanded, { body => $rebuilt, label => "$source_index.original" };
    return @expanded;
}

my @units;
for my $source_index (0 .. $#source_declarations) {
    push @units,
        split_pattern_declaration($source_declarations[$source_index], $source_index);
}

make_path($output_dir);
unlink glob("$output_dir/FunsPart*.lean");
my $previous = "$namespace.Types";
my @manifest;
for my $index (0 .. $#units) {
    my $part = sprintf('FunsPart%02d', $index);
    my $path = "$output_dir/$part.lean";
    open my $part_fh, '>', $path or die "open $path: $!\n";
    print {$part_fh} "-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE\n";
    print {$part_fh} "import $previous\n";
    print {$part_fh} "open Aeneas Aeneas.Std Result ControlFlow Error\n";
    print {$part_fh} "set_option linter.dupNamespace false\n";
    print {$part_fh} "set_option linter.hashCommand false\n";
    print {$part_fh} "set_option linter.unusedVariables false\n";
    print {$part_fh} "set_option maxHeartbeats 8000000\n";
    print {$part_fh} "set_option maxRecDepth 10000\n\n";
    print {$part_fh} "namespace $namespace\n\n";
    print {$part_fh} $units[$index]->{body};
    print {$part_fh} "\nend $namespace\n";
    close $part_fh;
    push @manifest, sprintf(
        "%02d %s %s %s\n", $index, sha256_hex($units[$index]->{body}),
        $part, $units[$index]->{label});
    $previous = "$namespace.$part";
}

my $facade = "$output_dir/Funs.lean";
open my $facade_fh, '>', $facade or die "open $facade: $!\n";
print {$facade_fh} "-- IMPORT FACADE FOR THE DECLARATION-PRESERVING GENERATED SPLIT\n";
print {$facade_fh} "import $previous\n";
close $facade_fh;

my $manifest_path = "$output_dir/FunsSplitManifest.txt";
open my $manifest_fh, '>', $manifest_path
    or die "open $manifest_path: $!\n";
print {$manifest_fh} "input_sha256 " . sha256_hex($text) . "\n";
print {$manifest_fh} "source_declaration_count " .
    scalar(@source_declarations) . "\n";
print {$manifest_fh} "split_module_count " . scalar(@units) . "\n";
print {$manifest_fh} @manifest;
close $manifest_fh;

print "split generated Funs into " . scalar(@units) .
    " bounded-elaboration modules\n";
