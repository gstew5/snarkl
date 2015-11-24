set terminal pngcairo nocrop enhanced size 1000,320 font "arial,12"
set output 'benchmark-data-112415.png'
set boxwidth 1 relative
set style fill   solid 1 border lt -1
set key outside right top vertical Left reverse noenhanced autotitle columnhead nobox
set key invert samplen 4 spacing 1 width 0 height 0
set style histogram clustered title textcolor lt -1
set datafile missing '-'
set style data histograms
set xtics border in scale 0,0 nomirror rotate by -25  autojustify
set xtics norangelimit
set xtics ("FixedMatrix-Simpl" 0, "FixedMatrix-NoSimpl" 1, "FixedMatrix-Interp" 2, "InputMatrices-Simpl" 3, "InputMatrices-NoSimpl" 4, "InputMatrices-Interp" 5, "Keccak-Simpl" 6, "Keccak-NoSimpl" 7, "Keccak-Interp" 8, "List-Simpl" 9, "List-NoSimpl" 10, "List-Interp" 11)
set title "Benchmark Breakdown by Phase"
set logscale y 10
set yrange [ 0.01 : 100 ] noreverse nowriteback
set ylabel "sec"
set style fill pattern
x = 0.0
i = 0
plot 'benchmark-data-112415.dat' using 2:xtic(1), for [i=3:9] '' using i
