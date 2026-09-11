# Encoding baseline

What every encoder costs to run, and what it emits, over the shapes in
`encoding.rs`. Regenerate both halves with:

```
cargo bench -p pindakaas --bench encoding                    # timings
PINDAKAAS_SIZES=1 cargo bench -p pindakaas --bench encoding  # sizes
```

Taken on an Apple M4, rustc 1.98.0, `--release`, at the tip of the encoding
performance work: the sizes are what they were before it, since none of those
changes altered the CNF, and the times are between a half and a third of what
they were. Absolute times move with the machine; the ratios between encoders
are what the table is for. Time is the fastest sample divan saw, which is the
one least disturbed by the rest of the machine. Throughput is clauses per
second of that sample — a slow encoder producing a large encoding is a
different problem from a slow one producing a small.

`vars`, `clauses` and `literals` count what the linear encoder added, not what
the database already held: the literals of a term and the at-most-one
constraints over a group are built before the measurement starts.

## What the shapes are

| Shape | Terms | Bound |
|---|---|---|
| `card-N` | `N` literals of coefficient one | `N/2` |
| `pb-small-10`, `pb-large-10` | 10 literals, coefficients in `1..=8` and `1..=512` | every second coefficient |
| `pb-coprime-8` | the primes `3..=23` | every second coefficient |
| `pb-wide-40` | 40 literals, coefficients in `1..=4` | every second coefficient |
| `amo-6x4` | 6 exactly-one groups of 4 weights | a middle choice from each |
| `int-6x40` | 6 integer variables over `0..=40` | half the total |
| `pb-nN` | `N` literals, coefficients in `1..=8` | every second coefficient |
| `pb-kK` | 8 literals, coefficients up to `8`…`4096` | every second coefficient |

Bounds are subset sums by construction: an equality against an unreachable
bound is settled by propagation inside a domain consistent encoder, which
measures the detection rather than the encoding.

## The table

```
         shape  cmp     enc    vars  clauses  literals        time   clauses/s
       card-10   <=   adder      14       93       323      3.71 µs     25.09M
       card-10   <= diagram      25       66       152     12.45 µs      5.30M
       card-10   <=     seq      45      126       284      9.42 µs     13.38M
       card-10   <=    tree      23       69       161      7.83 µs      8.81M
       card-10   <=   radix      41      163       383     20.70 µs      7.87M
       card-10   <=    wdog      32       93       216     11.41 µs      8.15M
       card-10   <=  wdog-l     360      980      2320     98.66 µs      9.93M
       card-10   <=    sort      24       65       150      7.83 µs      8.30M
       card-10   ==   adder      12       87       295      3.71 µs     23.47M
       card-10   == diagram      25      116       272     17.79 µs      6.52M
       card-10   ==     seq      35      159       373     13.95 µs     11.40M
       card-10   ==    tree      23      118       284     11.74 µs     10.05M
       card-10   ==   radix      41      165       385     21.20 µs      7.78M
       card-10   ==    wdog      74      226       512     25.49 µs      8.87M
       card-10   ==  wdog-l     730     2000      4720    204.20 µs      9.79M
       card-10   ==    sort      24      114       268     10.74 µs     10.61M
       card-20   <=   adder      35      231       807      7.21 µs     32.05M
       card-20   <= diagram     100      281       652     33.99 µs      8.27M
       card-20   <=     seq     190      551      1264     28.74 µs     19.17M
       card-20   <=    tree      66      235       575     18.83 µs     12.48M
       card-20   <=   radix     116      505      1200     50.58 µs      9.98M
       card-20   <=    wdog      84      302       739     26.54 µs     11.38M
       card-20   <=  wdog-l    1900     6820     17060    477.70 µs     14.28M
       card-20   <=    sort      68      218       526     18.79 µs     11.60M
       card-20   ==   adder      31      218       756      7.17 µs     30.42M
       card-20   == diagram     100      481      1142     47.16 µs     10.20M
       card-20   ==     seq     145      689      1638     42.74 µs     16.12M
       card-20   ==    tree      66      411      1037     29.91 µs     13.74M
       card-20   ==   radix     116      507      1201     50.87 µs      9.97M
       card-20   ==    wdog     188      684      1638     56.08 µs     12.20M
       card-20   ==  wdog-l    3820    13720     34280    962.10 µs     14.26M
       card-20   ==    sort      68      386       952     27.20 µs     14.19M
       card-40   <=   adder      75      505      1779     14.62 µs     34.54M
       card-40   <= diagram     400     1161      2702    103.20 µs     11.25M
       card-40   <=     seq     780     2301      5324     92.49 µs     24.88M
       card-40   <=    tree     172      784      2014     47.45 µs     16.52M
       card-40   <=   radix     234     1229      3041     97.16 µs     12.65M
       card-40   <=    wdog     208      985      2540     61.83 µs     15.93M
       card-40   <=  wdog-l    9360    46760    123160      2.40 ms     19.50M
       card-40   <=    sort     176      714      1808     45.79 µs     15.59M
       card-40   ==   adder      70      489      1717     14.08 µs     34.73M
       card-40   == diagram     400     1961      4682    142.70 µs     13.74M
       card-40   ==     seq     590     2874      6868    135.40 µs     21.23M
       card-40   ==    tree     172     1411      3725     78.91 µs     17.88M
       card-40   ==   radix     234     1231      3042     97.04 µs     12.69M
       card-40   ==    wdog     456     2130      5400    134.10 µs     15.88M
       card-40   ==  wdog-l   18760    93680    246640      4.92 ms     19.02M
       card-40   ==    sort     176     1290      3340     70.79 µs     18.22M
       card-80   <=   adder     155     1059      3751     27.79 µs     38.11M
       card-80   <= diagram    1600     4721     11002    337.00 µs     14.01M
       card-80   <=     seq    3160     9401     21844    322.30 µs     29.17M
       card-80   <=    tree     424     2670      7176    125.20 µs     21.33M
       card-80   <=   radix     572     3339      8419    223.10 µs     14.97M
       card-80   <=    wdog     496     3331      9002    161.10 µs     20.68M
       card-80   <=  wdog-l   44240   328560    903600     13.84 ms     23.74M
       card-80   <=    sort     432     2386      6332    116.20 µs     20.53M
       card-80   ==   adder     149     1040      3678     27.45 µs     37.89M
       card-80   == diagram    1600     7921     18962    486.70 µs     16.27M
       card-80   ==     seq    2380    11744     28128    473.50 µs     24.80M
       card-80   ==    tree     424     4947     13589    217.40 µs     22.76M
       card-80   ==   radix     572     3340      8419    222.50 µs     15.01M
       card-80   ==    wdog    1072     6982     18644    338.20 µs     20.64M
       card-80   ==  wdog-l   88560   657440   1807840     28.65 ms     22.95M
       card-80   ==    sort     432     4418     11956    193.90 µs     22.78M
   pb-small-10   <=   adder      23      153       532      3.54 µs     43.22M
   pb-small-10   <= diagram      29       89       202     16.16 µs      5.51M
   pb-small-10   <=     seq     198      521      1180     21.87 µs     23.82M
   pb-small-10   <=    tree      53      174       426     16.24 µs     10.71M
   pb-small-10   <=   radix     103      362       831     52.08 µs      6.95M
   pb-small-10   <=    wdog      54      141       326     21.41 µs      6.59M
   pb-small-10   <=  wdog-l     527     1323      3094    179.10 µs      7.39M
   pb-small-10   ==   adder      18      135       450      3.25 µs     41.55M
   pb-small-10   == diagram      31      143       332     22.04 µs      6.49M
   pb-small-10   ==     seq     175      752      1785     36.74 µs     20.47M
   pb-small-10   ==    tree      53      291       748     24.83 µs     11.72M
   pb-small-10   ==   radix     103      364       830     52.08 µs      6.99M
   pb-small-10   ==    wdog     128      348       797     47.58 µs      7.31M
   pb-small-10   ==  wdog-l    1083     2753      6437    370.40 µs      7.43M
   pb-large-10   <=   adder      65      435      1531      8.12 µs     53.55M
   pb-large-10   <= diagram      29       86       198     16.12 µs      5.33M
   pb-large-10   <=     seq    7326    18561     41836    491.10 µs     37.79M
   pb-large-10   <=    tree     228      497      1206     66.70 µs      7.45M
   pb-large-10   <=   radix     327     1062      2446    159.80 µs      6.65M
   pb-large-10   <=    wdog     168      484      1158     56.16 µs      8.62M
   pb-large-10   <=  wdog-l    1525     4264     10213    479.30 µs      8.90M
   pb-large-10   ==   adder      55      399      1362      8.00 µs     49.88M
   pb-large-10   == diagram      14       61       133     17.24 µs      3.54M
   pb-large-10   ==     seq    4848    18949     44941    643.30 µs     29.46M
   pb-large-10   ==    tree     228      763      1963    122.20 µs      6.24M
   pb-large-10   ==   radix     327     1068      2440    162.00 µs      6.59M
   pb-large-10   ==    wdog     355     1037      2471    118.00 µs      8.79M
   pb-large-10   ==  wdog-l    3103     8701     20837    984.10 µs      8.84M
  pb-coprime-8   <=   adder      37      238       823      5.04 µs     47.22M
  pb-coprime-8   <= diagram      21       66       150     12.58 µs      5.25M
  pb-coprime-8   <=     seq     294      733      1646     27.08 µs     27.07M
  pb-coprime-8   <=    tree      36       76       169      9.21 µs      8.25M
  pb-coprime-8   <=   radix     181      571      1296     87.70 µs      6.51M
  pb-coprime-8   <=    wdog      90      248       587     30.12 µs      8.23M
  pb-coprime-8   <=  wdog-l     567     1548      3684    178.40 µs      8.68M
  pb-coprime-8   ==   adder      31      219       742      4.71 µs     46.52M
  pb-coprime-8   == diagram      18       81       184     15.29 µs      5.30M
  pb-coprime-8   ==     seq     175      652      1536     32.04 µs     20.35M
  pb-coprime-8   ==    tree      36      121       280     13.45 µs      9.00M
  pb-coprime-8   ==   radix     181      574      1293     86.49 µs      6.64M
  pb-coprime-8   ==    wdog     193      546      1284     63.20 µs      8.64M
  pb-coprime-8   ==  wdog-l    1172     3204      7614    373.70 µs      8.57M
    pb-wide-40   <=   adder      92      635      2251     11.45 µs     55.46M
    pb-wide-40   <= diagram     550     1650      3836    145.40 µs     11.35M
    pb-wide-40   <=     seq    2067     6027     13961    196.90 µs     30.61M
    pb-wide-40   <=    tree     272     1845      5020    107.90 µs     17.10M
    pb-wide-40   <=   radix     369     1702      4133    160.20 µs     10.62M
    pb-wide-40   <=    wdog     269     1202      3095     86.74 µs     13.86M
    pb-wide-40   <=  wdog-l   11085    50410    131205      3.26 ms     15.44M
    pb-wide-40   ==   adder      87      621      2180     11.62 µs     53.44M
    pb-wide-40   == diagram     563     2775      6622    220.40 µs     12.59M
    pb-wide-40   ==     seq    1490     7170     17158    280.10 µs     25.60M
    pb-wide-40   ==    tree     272     3414      9509    179.00 µs     19.07M
    pb-wide-40   ==   radix     369     1705      4135    161.40 µs     10.56M
    pb-wide-40   ==    wdog     581     2599      6609    188.40 µs     13.80M
    pb-wide-40   ==  wdog-l   22256   101727    264868      6.61 ms     15.38M
       amo-6x4   <=   adder      78      536      1893      9.83 µs     54.52M
       amo-6x4   <= diagram      44      177       441     17.87 µs      9.90M
       amo-6x4   <=     seq     170      644      1601     22.29 µs     28.89M
       amo-6x4   <=    tree      54      197       495     12.45 µs     15.82M
       amo-6x4   <=   radix     179      667      1556     83.16 µs      8.02M
       amo-6x4   <=    wdog     109      319       751     30.62 µs     10.42M
       amo-6x4   <=  wdog-l    2096     5763     13502    565.90 µs     10.18M
       amo-6x4   ==   adder      72      515      1799     10.00 µs     51.51M
       amo-6x4   == diagram      42      308       780     25.79 µs     11.94M
       amo-6x4   ==     seq     106      717      1864     30.62 µs     23.42M
       amo-6x4   ==    tree      54      345       891     20.12 µs     17.15M
       amo-6x4   ==   radix     179      670      1552     83.12 µs      8.06M
       amo-6x4   ==    wdog     255      748      1732     67.24 µs     11.12M
       amo-6x4   ==  wdog-l    4253    11697     27372      1.12 ms     10.40M
      int-6x40   <=   adder      92      413      1445      8.87 µs     46.54M
      int-6x40   <= diagram     600    10669     30938    435.90 µs     24.48M
      int-6x40   <=     seq     840    17629     51178    504.50 µs     34.94M
      int-6x40   <=    tree     600    11490     33360    325.40 µs     35.31M
      int-6x40   <=   radix     694     2087      4873    172.60 µs     12.09M
      int-6x40   <=    wdog     428     6000     12426    114.20 µs     52.54M
      int-6x40   <=  wdog-l   39906   221346    481626     15.55 ms     14.23M
      int-6x40   ==   adder      85      386      1314      8.66 µs     44.55M
      int-6x40   == diagram     600    20749     60698    756.20 µs     27.44M
      int-6x40   ==     seq     720    27430     80459    820.70 µs     33.42M
      int-6x40   ==    tree     600    22311     65421    651.10 µs     34.27M
      int-6x40   ==   radix     694     2091      4865    169.90 µs     12.31M
      int-6x40   ==    wdog    1096     8760     18606    244.10 µs     35.89M
      int-6x40   ==  wdog-l   80052   439452    957006     31.90 ms     13.78M
         pb-n8   <=   adder      19      119       401      2.87 µs     41.41M
         pb-n8   <= diagram      13       44        97     10.29 µs      4.28M
         pb-n8   <=     seq      63      156       344      9.92 µs     15.73M
         pb-n8   <=    tree      21       50       109      8.00 µs      6.25M
         pb-n8   <=   radix      85      271       604     45.83 µs      5.91M
         pb-n8   <=    wdog      39      105       241     17.12 µs      6.13M
         pb-n8   <=  wdog-l     314      807      1889    106.90 µs      7.55M
         pb-n8   ==   adder      16      112       375      2.87 µs     38.97M
         pb-n8   == diagram      11       50       112     12.87 µs      3.89M
         pb-n8   ==     seq      54      214       502     14.66 µs     14.60M
         pb-n8   ==    tree      21       80       182     10.95 µs      7.31M
         pb-n8   ==   radix      85      273       604     45.41 µs      6.01M
         pb-n8   ==    wdog      90      256       585     34.54 µs      7.41M
         pb-n8   ==  wdog-l     650     1693      3954    218.80 µs      7.74M
        pb-n16   <=   adder      42      285       998      5.67 µs     50.31M
        pb-n16   <= diagram     122      366       847     41.24 µs      8.87M
        pb-n16   <=     seq     495     1365      3123     49.99 µs     27.31M
        pb-n16   <=    tree     100      303       724     26.29 µs     11.53M
        pb-n16   <=   radix     186      711      1662     84.74 µs      8.39M
        pb-n16   <=    wdog     110      355       858     36.99 µs      9.60M
        pb-n16   <=  wdog-l    1818     5746     14063    530.40 µs     10.83M
        pb-n16   ==   adder      37      266       916      5.37 µs     49.50M
        pb-n16   == diagram     123      602      1429     59.91 µs     10.05M
        pb-n16   ==     seq     362     1621      3861     71.95 µs     22.53M
        pb-n16   ==    tree     100      510      1267     39.87 µs     12.79M
        pb-n16   ==   radix     186      713      1662     83.20 µs      8.57M
        pb-n16   ==    wdog     240      794      1902     78.04 µs     10.17M
        pb-n16   ==  wdog-l    3661    11602     28373      1.09 ms     10.62M
        pb-n32   <=   adder      96      649      2287     11.74 µs     55.28M
        pb-n32   <= diagram     712     2130      4960    177.70 µs     11.99M
        pb-n32   <=     seq    2139     6172     14276    203.00 µs     30.40M
        pb-n32   <=    tree     267     1435      3812     93.29 µs     15.38M
        pb-n32   <=   radix     452     1970      4742    195.50 µs     10.08M
        pb-n32   <=    wdog     271     1172      2998     85.87 µs     13.65M
        pb-n32   <=  wdog-l    9280    39800    102620      2.60 ms     15.29M
        pb-n32   ==   adder      90      630      2208     11.54 µs     54.59M
        pb-n32   == diagram     716     3559      8516    265.40 µs     13.41M
        pb-n32   ==     seq    1629     7762     18572    296.40 µs     26.19M
        pb-n32   ==    tree     267     2602      7115    151.70 µs     17.15M
        pb-n32   ==   radix     452     1974      4745    196.70 µs     10.04M
        pb-n32   ==    wdog     577     2503      6341    180.80 µs     13.84M
        pb-n32   ==  wdog-l   18428    79828    206040      5.31 ms     15.04M
        pb-n64   <=   adder     190     1294      4578     21.87 µs     59.17M
        pb-n64   <= diagram    3049     9135     21298    623.90 µs     14.64M
        pb-n64   <=     seq    8631    25404     59024    746.80 µs     34.02M
        pb-n64   <=    tree     701     8693     24746    494.50 µs     17.58M
        pb-n64   <=   radix     892     4443     11004    377.70 µs     11.76M
        pb-n64   <=    wdog     615     3555      9487    202.50 µs     17.56M
        pb-n64   <=  wdog-l   41052   242264    651364     12.52 ms     19.35M
        pb-n64   ==   adder     183     1274      4500     21.95 µs     58.04M
        pb-n64   == diagram    3061    15267     36592    945.00 µs     16.16M
        pb-n64   ==     seq    6658    32523     77944      1.14 ms     28.63M
        pb-n64   ==    tree     701    16640     48070    799.70 µs     20.81M
        pb-n64   ==   radix     892     4446     11005    380.90 µs     11.67M
        pb-n64   ==    wdog    1298     7433     19681    417.90 µs     17.79M
        pb-n64   ==  wdog-l   82254   486534   1308234     25.84 ms     18.83M
        pb-k11   <=   adder      12       79       268      2.17 µs     36.49M
        pb-k11   <= diagram      13       40        89     10.00 µs      4.00M
        pb-k11   <=     seq      77      191       423     10.79 µs     17.70M
        pb-k11   <=    tree      23       55       122      8.37 µs      6.57M
        pb-k11   <=   radix      64      194       430     35.12 µs      5.52M
        pb-k11   <=    wdog      23       59       132     12.91 µs      4.57M
        pb-k11   <=  wdog-l     220      540      1252     86.33 µs      6.26M
        pb-k11   ==   adder      10       75       244      2.15 µs     34.97M
        pb-k11   == diagram      12       53       120     13.24 µs      4.00M
        pb-k11   ==     seq      69      277       652     17.08 µs     16.22M
        pb-k11   ==    tree      23       88       203     11.62 µs      7.57M
        pb-k11   ==   radix      64      197       432     37.91 µs      5.20M
        pb-k11   ==    wdog      63      170       378     29.12 µs      5.84M
        pb-k11   ==  wdog-l     454     1104      2542    180.50 µs      6.12M
       pb-k131   <=   adder      36      249       874      4.92 µs     50.66M
       pb-k131   <= diagram      19       59       134     11.62 µs      5.08M
       pb-k131   <=     seq     917     2295      5175     69.16 µs     33.18M
       pb-k131   <=    tree      39       80       179      9.79 µs      8.17M
       pb-k131   <=   radix     164      512      1159     81.83 µs      6.26M
       pb-k131   <=    wdog      91      281       676     31.70 µs      8.86M
       pb-k131   <=  wdog-l     684     1955      4692    216.70 µs      9.02M
       pb-k131   ==   adder      30      225       760      4.83 µs     46.55M
       pb-k131   == diagram       3       16        28     10.12 µs      1.58M
       pb-k131   ==     seq     593     2258      5342     86.66 µs     26.06M
       pb-k131   ==    tree      39      124       287     13.79 µs      8.99M
       pb-k131   ==   radix     164      517      1158     82.83 µs      6.24M
       pb-k131   ==    wdog     190      587      1395     65.74 µs      8.93M
       pb-k131   ==  wdog-l    1390     3978      9535    441.40 µs      9.01M
       pb-k963   <=   adder      51      337      1186      6.71 µs     50.25M
       pb-k963   <= diagram      16       46       106     10.66 µs      4.32M
       pb-k963   <=     seq    6741    17271     39287    451.70 µs     38.24M
       pb-k963   <=    tree      41       81       183      9.75 µs      8.31M
       pb-k963   <=   radix     283      890      2019    134.40 µs      6.62M
       pb-k963   <=    wdog     131      389       940     44.62 µs      8.72M
       pb-k963   <=  wdog-l     901     2516      6015    291.70 µs      8.63M
       pb-k963   ==   adder      43      310      1048      6.58 µs     47.10M
       pb-k963   == diagram       0        8         8      8.41 µs      0.95M
       pb-k963   ==     seq    4572    18313     43490    600.90 µs     30.48M
       pb-k963   ==    tree      41      127       295     14.04 µs      9.05M
       pb-k963   ==   radix     283      894      2012    135.90 µs      6.58M
       pb-k963   ==    wdog     262      788      1886     89.70 µs      8.78M
       pb-k963   ==  wdog-l    1828     5122     12239    592.40 µs      8.65M
      pb-k8131   <=   adder      71      483      1722      9.33 µs     51.76M
      pb-k8131   <= diagram      16       50       113     10.79 µs      4.63M
      pb-k8131   <=     seq   56917   142199    320887      3.63 ms     39.21M
      pb-k8131   <=    tree      39       79       177      9.66 µs      8.17M
      pb-k8131   <=   radix     422     1348      3109    206.00 µs      6.54M
      pb-k8131   <=    wdog     189      552      1325     62.12 µs      8.89M
      pb-k8131   <=  wdog-l    1340     3702      8835    431.70 µs      8.58M
      pb-k8131   ==   adder      60      443      1502      8.96 µs     49.46M
      pb-k8131   == diagram       0        8         8      8.79 µs      0.91M
      pb-k8131   ==     seq   44417   176578    419230      5.54 ms     31.88M
      pb-k8131   ==    tree      39      124       287     14.08 µs      8.81M
      pb-k8131   ==   radix     422     1355      3095    207.20 µs      6.54M
      pb-k8131   ==    wdog     386     1136      2714    124.50 µs      9.12M
      pb-k8131   ==  wdog-l    2714     7502     17895    853.40 µs      8.79M
```

## What the encodings cost the solver

`examples/encoding_quality.rs`, run as:

```
cargo run --release --example encoding_quality
```

`conflicts` is the least conflict budget CaDiCaL needs before it decides the
instance, found by doubling and then bisecting its `conflicts` limit. It is
deterministic where wall time is not, and it is what moves when an encoding's
propagation strength moves. `t/o` is a solve that ran out its 90 second budget,
which says nothing about the conflict count beyond "more than this machine will
wait for". Time is the best of up to three unlimited solves.

```
     instance     enc    vars  clauses  conflicts      time   result
   pigeonhole   adder     224     1254   >1048576  56637.5ms    unsat
   pigeonhole diagram     287      855      14025     99.9ms    unsat
   pigeonhole     seq     301      897      13401     92.9ms    unsat
   pigeonhole    tree     287      862      22251    138.7ms    unsat
   pigeonhole   radix     301     1198      82614    528.4ms    unsat
   pigeonhole    wdog     308      911      23552    150.9ms    unsat
   pigeonhole  wdog-l    5985    20280        t/o  90000.1ms      t/o
   pigeonhole    sort     287      862      40048    255.4ms    unsat
 market-split   adder     172     1085        331      1.6ms      sat
 market-split diagram    1316     6426        151      3.0ms      sat
 market-split     seq    6346    29314         16      1.5ms      sat
 market-split    tree     975    26808          1      0.3ms      sat
 market-split   radix     847     3245        202      2.3ms      sat
 market-split    wdog    1001     3544        363      4.6ms      sat
 market-split  wdog-l   18513    65063         40     10.5ms      sat
     knapsack   adder     718     4531        t/o  90000.0ms      t/o
     knapsack diagram    2860    16886     122124   3957.9ms    unsat
     knapsack     seq    8363    48471     111818   4049.5ms    unsat
     knapsack    tree    2222    62242      69918   1761.3ms    unsat
     knapsack   radix    1491     6271      46347    703.4ms    unsat
     knapsack    wdog    1145     4417        t/o  90013.1ms      t/o
     knapsack  wdog-l   62211   240982        t/o  90008.9ms      t/o
      auction   adder     364     2691       1550     18.4ms    unsat
      auction diagram   29613    89181        179    230.9ms    unsat
      auction     seq  224251   653464        183   2075.4ms    unsat
      auction    tree   11297  4204016        228   1771.0ms    unsat
      auction   radix    1848     8426        513     12.7ms    unsat
      auction    wdog    1142     6521        228      3.3ms    unsat
      auction  wdog-l   43250   236130        199    257.6ms    unsat
```
