set terminal pngcairo nocrop enhanced size 520,320 font "arial,12"
set output 'ratio.png'
set title "Crypto vs. Witness Latency"
set xlabel "Proof Generation and Verification (s)"
set ylabel "Witness Generation (s)"
set xrange [0.1:100]
set yrange [0.1:100]
set logscale x
set logscale y
set key left
f(x) = x
plot 'ratio.dat' using 7:8 with points title 'Input Matrices',\
     'ratio.dat' using 1:2 with points title 'Keccak-f800',\
     'ratio.dat' using 3:4 with points title 'Map List',\
     'ratio.dat' using 5:6 with points title 'Fixed Matrix',\
     f(x) lt -1 title '' 

