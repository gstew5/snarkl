set terminal png nocrop enhanced size 320,320 font "arial,8"
set output 'benchmark-data-112415.png'
set boxwidth 0.85 absolute
set style fill   solid 1.00 border lt -1
set key outside right top vertical Left reverse noenhanced autotitle columnhead nobox
set key invert samplen 4 spacing 1 width 0 height 0
set style histogram rowstacked title textcolor lt -1
set datafile missing '-'
set style data histograms
set xtics border in scale 0,0 nomirror rotate by -25  autojustify
set xtics norangelimit
set xtics ("Simpl" 0, "NoSimpl" 1, "Interp" 2)
set title "Compiler Phases"
set yrange [ 0 : 105 ] noreverse nowriteback
set ylabel "sec"
set style fill pattern border
x = 0.0
i = 0
plot 'benchmark-data-112415.dat' using 2:xtic(1), for [i=3:9] '' using i
