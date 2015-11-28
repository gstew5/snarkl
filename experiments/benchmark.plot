set terminal pngcairo nocrop enhanced size 1000,320 font "arial,12"
set output 'benchmark-data.png'
set boxwidth 0.75 relative
set style fill   solid 1 border lt -1
set key outside right top vertical Left reverse noenhanced autotitle columnhead nobox
set key invert samplen 4 spacing 1 width 0 height 0
set style histogram clustered title textcolor lt -1
set datafile missing '-'
set style data histograms
set xtics border in scale 0,0 nomirror rotate by -25  autojustify
set xtics norangelimit
set title "Benchmark Breakdown by Phase"
set yrange [ 0.005 : 100 ] noreverse nowriteback
set ylabel "sec"
set logscale y 10
set style line 100 lt 1 lc rgb "gray" lw 2
set style line 101 lt 0.5 lc rgb "gray" lw 0
set grid mytics ytics ls 100, ls 101
set style fill pattern
plot 'benchmark-data.dat' using 2:xtic(1) title columnheader(2),\
  for [i=3:8] '' using i title columnheader(i)
