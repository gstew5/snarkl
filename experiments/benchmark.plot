set terminal png nocrop enhanced size 450,320 font "arial,8"
set output 'benchmark-data-9182015.png'
set boxwidth 0.75 absolute
set style fill   solid 1.00 border lt -1
set key outside right top vertical Left reverse noenhanced autotitle columnhead nobox
set key invert samplen 4 spacing 1 width 0 height 0
set style histogram rowstacked title textcolor lt -1
set datafile missing '-'
set style data histograms
set xtics border in scale 0,0 nomirror rotate by -25  autojustify
set xtics norangelimit
set xtics ("Simpl" 0, "NoSimpl" 1, "Interp" 2)
set title "SHA3 Keccak-f(200)"
set yrange [ 0 : 3500 ] noreverse nowriteback
set ylabel "ms"
x = 0.0
i = 8
plot 'benchmark-data-9182015.dat' using 2:xtic(1), for [i=3:8] '' using i
