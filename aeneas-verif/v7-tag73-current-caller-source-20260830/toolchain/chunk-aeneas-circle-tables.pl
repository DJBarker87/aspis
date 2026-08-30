#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use File::Basename qw(dirname);

@ARGV == 2 or die "usage: $0 CALLER_FUNS CALLER_MODULE\n";
my ($caller_funs, $caller) = @ARGV;
my $caller_dir = dirname($caller_funs);

open my $input, '<', $caller_funs or die "open $caller_funs: $!\n";
local $/;
my $source = <$input>;
close $input or die "close $caller_funs: $!\n";

my @tables = (
    [ 'RATE512_CIRCLE_LOW8_WINDOW', 256 ],
    [ 'RATE512_CIRCLE_HIGH9_WINDOW', 512 ],
    [ 'V6_CIRCLE_LOW6_WINDOW', 64 ],
    [ 'V6_CIRCLE_MIDDLE6_WINDOW', 64 ],
    [ 'V6_CIRCLE_HIGH6_WINDOW', 64 ],
);
my $chunk_size = 16;

sub module_name {
    my ($table, $index) = @_;
    return sprintf('CircleTable_%s_Chunk%02d', $table, $index);
}

sub write_file {
    my ($path, $contents) = @_;
    open my $output, '>', $path or die "open $path: $!\n";
    print {$output} $contents or die "write $path: $!\n";
    close $output or die "close $path: $!\n";
}

my $support_module = 'CircleTableSupport';
write_file(
    "$caller_dir/$support_module.lean",
    "import $caller.FunsExternal\n\n" .
    "open Aeneas Aeneas.Std Result ControlFlow Error\n" .
    "set_option linter.dupNamespace false\n" .
    "set_option linter.hashCommand false\n" .
    "set_option linter.unusedVariables false\n" .
    "noncomputable section\n\n" .
    "namespace $caller\n" .
    "namespace staged_circle_tables\n\n" .
    "def circle_pair (x y : Std.U32) : Array Std.U32 2#usize :=\n" .
    "  ⟨[x, y], by rfl⟩\n\n" .
    "def append16 {T : Type} (left right : Array T 16#usize) :\n" .
    "    Array T 32#usize :=\n" .
    "  ⟨left.val ++ right.val, by\n" .
    "    simp only [List.length_append, Array.length_eq]\n" .
    "    rfl⟩\n\n" .
    "def append32 {T : Type} (left right : Array T 32#usize) :\n" .
    "    Array T 64#usize :=\n" .
    "  ⟨left.val ++ right.val, by\n" .
    "    simp only [List.length_append, Array.length_eq]\n" .
    "    rfl⟩\n\n" .
    "def append64 {T : Type} (left right : Array T 64#usize) :\n" .
    "    Array T 128#usize :=\n" .
    "  ⟨left.val ++ right.val, by\n" .
    "    simp only [List.length_append, Array.length_eq]\n" .
    "    rfl⟩\n\n" .
    "def append128 {T : Type} (left right : Array T 128#usize) :\n" .
    "    Array T 256#usize :=\n" .
    "  ⟨left.val ++ right.val, by\n" .
    "    simp only [List.length_append, Array.length_eq]\n" .
    "    rfl⟩\n\n" .
    "def append256 {T : Type} (left right : Array T 256#usize) :\n" .
    "    Array T 512#usize :=\n" .
    "  ⟨left.val ++ right.val, by\n" .
    "    simp only [List.length_append, Array.length_eq]\n" .
    "    rfl⟩\n\n" .
    "end staged_circle_tables\n" .
    "end $caller\n"
);

my @compile_order = ("$caller/$support_module.lean");
my @last_modules;
my @manifest = (
    "format=aspis-aeneas-circle-table-chunks-v1",
    "caller=$caller",
    "chunk_size=$chunk_size",
);

for my $spec (@tables) {
    my ($table, $expected_count) = @$spec;
    my $escaped = quotemeta($table);
    my $pattern = qr{
        (def\ aspis_core\.circle_fri\.$escaped\n
         \ \ :\ Array\ \(Array\ Std\.U32\ 2\#usize\)\ $expected_count\#usize\ :=\n)
        (?:\ \ let\ a\ :=\ Array\.repeat\ 2\#usize\ ([0-9]+)\#u32\n)?
        \ \ Array\.make\ $expected_count\#usize\ \[\n
        (.*?)
        ^\ \ \ \ \]\n
    }msx;

    my ($header, $repeat_value, $body);
    my $matches = 0;
    while ($source =~ /$pattern/g) {
        $matches++;
        ($header, $repeat_value, $body) = ($1, $2, $3);
    }
    $matches == 1
        or die "$table: expected one exact generated declaration, found $matches\n";

    my @tokens;
    while ($body =~ /(Array\.make\ 2#usize\ \[\ ([0-9]+)#u32,\ ([0-9]+)#u32\ \]|\ba\b)/g) {
        if ($1 eq 'a') {
            defined $repeat_value
                or die "$table: found repeat token without repeat binding\n";
            push @tokens, [ $repeat_value, $repeat_value, 'a' ];
        } else {
            push @tokens, [ $2, $3, "$2,$3" ];
        }
    }

    my $unparsed = $body;
    $unparsed =~ s/Array\.make\ 2#usize\ \[\ [0-9]+#u32,\ [0-9]+#u32\ \]//g;
    $unparsed =~ s/\ba\b//g;
    $unparsed =~ s/[\s,]//g;
    $unparsed eq ''
        or die "$table: unparsed generated entry syntax: $unparsed\n";
    @tokens == $expected_count
        or die "$table: expected $expected_count entries, found " . scalar(@tokens) . "\n";
    $expected_count % $chunk_size == 0
        or die "$table: count is not divisible by chunk size\n";

    my @chunk_defs;
    my $chunk_count = $expected_count / $chunk_size;
    for my $chunk_index (0 .. $chunk_count - 1) {
        my $module = module_name($table, $chunk_index);
        my $previous = $chunk_index == 0
            ? "$caller.$support_module"
            : "$caller." . module_name($table, $chunk_index - 1);
        my $def_name = "${table}_chunk" . sprintf('%02d', $chunk_index);
        my @entries;
        for my $entry_index (0 .. $chunk_size - 1) {
            my $token = $tokens[$chunk_index * $chunk_size + $entry_index];
            push @entries,
                "    circle_pair $token->[0]#u32 $token->[1]#u32";
        }
        my $entry_text = join(",\n", @entries);
        my $module_text =
            "import $previous\n\n" .
            "open Aeneas Aeneas.Std Result ControlFlow Error\n" .
            "set_option linter.dupNamespace false\n" .
            "set_option linter.hashCommand false\n" .
            "set_option linter.unusedVariables false\n" .
            "noncomputable section\n\n" .
            "namespace $caller\n" .
            "namespace staged_circle_tables\n\n" .
            "def $def_name : Array (Array Std.U32 2#usize) $chunk_size#usize :=\n" .
            "  ⟨[\n$entry_text\n  ], by rfl⟩\n\n" .
            "end staged_circle_tables\n" .
            "end $caller\n";
        write_file("$caller_dir/$module.lean", $module_text);
        push @compile_order, "$caller/$module.lean";
        push @chunk_defs, "staged_circle_tables.$def_name";
    }

    my $last_module = module_name($table, $chunk_count - 1);
    push @last_modules, "$caller.$last_module";
    my @joined = @chunk_defs;
    my $width = $chunk_size;
    while (@joined > 1) {
        @joined % 2 == 0
            or die "$table: non-binary chunk join at width $width\n";
        my @next;
        while (@joined) {
            my $left = shift @joined;
            my $right = shift @joined;
            push @next,
                "staged_circle_tables.append$width ($left) ($right)";
        }
        @joined = @next;
        $width *= 2;
    }
    $width == $expected_count
        or die "$table: joined width $width differs from $expected_count\n";
    my $replacement = $header . "  $joined[0]\n";
    my $changed = ($source =~ s/$pattern/$replacement/);
    $changed == 1
        or die "$table: exact generated declaration replacement failed\n";

    my $source_tokens = join("\n", map { $_->[2] } @tokens) . "\n";
    my $expanded_pairs = join("\n", map { "$_->[0],$_->[1]" } @tokens) . "\n";
    push @manifest,
        join(' ',
            "table=$table",
            "entries=$expected_count",
            "chunks=$chunk_count",
            "source_token_sha256=" . sha256_hex($source_tokens),
            "expanded_pair_sha256=" . sha256_hex($expanded_pairs));
}

write_file($caller_funs, $source);
write_file(
    "$caller_dir/CircleTableCompileOrder.txt",
    join("\n", @compile_order) . "\n"
);
write_file(
    "$caller_dir/CircleTableLastModules.txt",
    join("\n", @last_modules) . "\n"
);
write_file(
    "$caller_dir/CircleTableChunkManifest.txt",
    join("\n", @manifest) . "\n"
);

print "chunked five exact generated circle tables: PASS\n";
