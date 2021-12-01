#!/usr/bin/perl

use 5.010;
use Getopt::Long qw(GetOptions);
 
my $dir;
GetOptions('from=s' => \$dir) or die "Usage: $0 --from runs\n";

if(length($dir) == 0) {
  die "Usage: $0 --from runs\n";
}

if(!(-e $dir and -d $dir)) {
  die "$dir not found.\n";
}

my $geo_mean_of_sat_cnt = 1;
my $geo_mean_of_gselect = 1;
my $geo_mean_of_gshare = 1;

my $num_files = 0;

foreach my $fp (glob("./$dir/*.txt")) {
  open my $fh, "<", $fp or die "can't read open '$fp': $OS_ERROR";
  $num_files++;
  while (<$fh>) {
    my $line = $_;
    if($line =~ m/^Final Score Run1_Conditional_MPPKI:   (\d+\.\d+)/) {
      $geo_mean_of_sat_cnt = $geo_mean_of_sat_cnt * $1;
    }
    if($line =~ m/^Final Score Run2_Conditional_MPPKI:   (\d+\.\d+)/) {
      $geo_mean_of_gselect = $geo_mean_of_gselect * $1;
    }
    if($line =~ m/^Final Score Run3_Conditional_MPPKI:   (\d+\.\d+)/) {
      $geo_mean_of_gshare = $geo_mean_of_gshare * $1;
    }
  }
  close $fh or die "can't read close '$fp': $OS_ERROR";
}

if($num_files == 0) {
  die "no .txt output file found in $dir\n";
}

$geo_mean_of_sat_cnt = int($geo_mean_of_sat_cnt**(1/$num_files) * 100) / 100;
$geo_mean_of_gselect = int($geo_mean_of_gselect**(1/$num_files) * 100) / 100;
$geo_mean_of_gshare = int($geo_mean_of_gshare**(1/$num_files) * 100) / 100;

print("Average score for Saturating Counter based predictor: $geo_mean_of_sat_cnt\n");
print("Average score for Gselect predictor: $geo_mean_of_gselect\n");
print("Average score for GShare predictor: $geo_mean_of_gshare\n");

my $sat_counter_score = 0;
my $gselect_score = 0;
my $gshare_score = 0;

if($num_files == 16) {
  print("The following performance score assumes that the 16 output files correspond to the 16 zipped traces ...\n");
  if($geo_mean_of_sat_cnt < 975) {
    $sat_counter_score = 30;
  } elsif($geo_mean_of_sat_cnt >= 975 && $geo_mean_of_sat_cnt < 1000) {
    $sat_counter_score = 25;
  } elsif($geo_mean_of_sat_cnt > 1000) {
    $sat_counter_score = 20;
  }

  if($geo_mean_of_gselect < 975) {
    $gselect_score = 30;
  } elsif($geo_mean_of_gselect >= 975 && $geo_mean_of_gselect < 1000) {
    $gselect_score = 25;
  } elsif($geo_mean_of_gselect > 1000) {
    $gselect_score = 20;
  }

  if($geo_mean_of_gshare < 580) {
    $gshare_score = 30;
  } elsif($geo_mean_of_gshare >= 580 && $geo_mean_of_gshare < 600) {
    $gshare_score = 25;
  } elsif($geo_mean_of_gshare > 600) {
    $gshare_score = 20;
  }

  my $total_score = $sat_counter_score + $gselect_score + $gshare_score;
  
  print("Total performance score: $total_score out of 90.\n");
}
