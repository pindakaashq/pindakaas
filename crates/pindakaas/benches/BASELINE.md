# Encoding baseline

What every encoder costs to run, and what it emits, over the shapes in
`encoding.rs`. Regenerate both halves with:

```
cargo bench -p pindakaas --bench encoding                    # timings
PINDAKAAS_SIZES=1 cargo bench -p pindakaas --bench encoding  # sizes
```

Taken on an Apple M4, rustc 1.98.0, `--release`. Absolute times move with the
machine; the ratios between encoders are what the table is for. Time is the
fastest sample divan saw, which is the one least disturbed by the rest of the
machine. Throughput is clauses per second of that sample — a slow encoder
producing a large encoding is a different problem from a slow one producing a
small.

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
       card-10   <=   adder      14       93       323      4.83 µs     19.25M
       card-10   <= diagram      25       66       152     18.91 µs      3.49M
       card-10   <=     seq      45      126       284     17.58 µs      7.17M
       card-10   <=    tree      23       69       161     15.20 µs      4.54M
       card-10   <=   radix      41      163       383     39.70 µs      4.11M
       card-10   <=    wdog      32       93       216     19.33 µs      4.81M
       card-10   <=  wdog-l     360      980      2320    175.60 µs      5.58M
       card-10   <=    sort      24       65       150     11.74 µs      5.54M
       card-10   ==   adder      12       87       295      4.71 µs     18.48M
       card-10   == diagram      25      116       272     28.74 µs      4.04M
       card-10   ==     seq      35      159       373     26.83 µs      5.93M
       card-10   ==    tree      23      118       284     24.08 µs      4.90M
       card-10   ==   radix      41      165       385     39.16 µs      4.21M
       card-10   ==    wdog      74      226       512     41.54 µs      5.44M
       card-10   ==  wdog-l     730     2000      4720    361.00 µs      5.54M
       card-10   ==    sort      24      114       268     17.66 µs      6.46M
       card-20   <=   adder      35      231       807     10.29 µs     22.45M
       card-20   <= diagram     100      281       652     58.12 µs      4.83M
       card-20   <=     seq     190      551      1264     61.29 µs      8.99M
       card-20   <=    tree      66      235       575     43.29 µs      5.43M
       card-20   <=   radix     116      505      1200    106.40 µs      4.75M
       card-20   <=    wdog      84      302       739     51.87 µs      5.82M
       card-20   <=  wdog-l    1900     6820     17060      1.01 ms      6.73M
       card-20   <=    sort      68      218       526     33.16 µs      6.57M
       card-20   ==   adder      31      218       756      9.92 µs     21.98M
       card-20   == diagram     100      481      1142     94.87 µs      5.07M
       card-20   ==     seq     145      689      1638     93.99 µs      7.33M
       card-20   ==    tree      66      411      1037     72.79 µs      5.65M
       card-20   ==   radix     116      507      1201    105.90 µs      4.79M
       card-20   ==    wdog     188      684      1638    108.00 µs      6.33M
       card-20   ==  wdog-l    3820    13720     34280      2.03 ms      6.76M
       card-20   ==    sort      68      386       952     54.66 µs      7.06M
       card-40   <=   adder      75      505      1779     20.99 µs     24.06M
       card-40   <= diagram     400     1161      2702    190.30 µs      6.10M
       card-40   <=     seq     780     2301      5324    222.70 µs     10.33M
       card-40   <=    tree     172      784      2014    126.90 µs      6.18M
       card-40   <=   radix     234     1229      3041    222.70 µs      5.52M
       card-40   <=    wdog     208      985      2540    146.40 µs      6.73M
       card-40   <=  wdog-l    9360    46760    123160      6.18 ms      7.56M
       card-40   <=    sort     176      714      1808     96.49 µs      7.40M
       card-40   ==   adder      70      489      1717     21.08 µs     23.20M
       card-40   == diagram     400     1961      4682    320.60 µs      6.12M
       card-40   ==     seq     590     2874      6868    328.50 µs      8.75M
       card-40   ==    tree     172     1411      3725    221.70 µs      6.36M
       card-40   ==   radix     234     1231      3042    221.10 µs      5.57M
       card-40   ==    wdog     456     2130      5400    304.40 µs      7.00M
       card-40   ==  wdog-l   18760    93680    246640     12.50 ms      7.49M
       card-40   ==    sort     176     1290      3340    171.20 µs      7.54M
       card-80   <=   adder     155     1059      3751     42.12 µs     25.14M
       card-80   <= diagram    1600     4721     11002    663.10 µs      7.12M
       card-80   <=     seq    3160     9401     21844    817.50 µs     11.50M
       card-80   <=    tree     424     2670      7176    393.90 µs      6.78M
       card-80   <=   radix     572     3339      8419    549.70 µs      6.07M
       card-80   <=    wdog     496     3331      9002    453.80 µs      7.34M
       card-80   <=  wdog-l   44240   328560    903600     41.19 ms      7.98M
       card-80   <=    sort     432     2386      6332    298.40 µs      8.00M
       card-80   ==   adder     149     1040      3678     41.49 µs     25.07M
       card-80   == diagram    1600     7921     18962      1.17 ms      6.80M
       card-80   ==     seq    2380    11744     28128      1.24 ms      9.45M
       card-80   ==    tree     424     4947     13589    728.50 µs      6.79M
       card-80   ==   radix     572     3340      8419    563.20 µs      5.93M
       card-80   ==    wdog    1072     6982     18644    936.70 µs      7.45M
       card-80   ==  wdog-l   88560   657440   1807840     84.12 ms      7.82M
       card-80   ==    sort     432     4418     11956    560.70 µs      7.88M
   pb-small-10   <=   adder      23      153       532      5.83 µs     26.23M
   pb-small-10   <= diagram      29       89       202     25.04 µs      3.55M
   pb-small-10   <=     seq     198      521      1180     51.87 µs     10.04M
   pb-small-10   <=    tree      53      174       426     32.41 µs      5.37M
   pb-small-10   <=   radix     103      362       831     96.16 µs      3.76M
   pb-small-10   <=    wdog      54      141       326     34.99 µs      4.03M
   pb-small-10   <=  wdog-l     527     1323      3094    301.20 µs      4.39M
   pb-small-10   ==   adder      18      135       450      5.33 µs     25.32M
   pb-small-10   == diagram      31      143       332     38.62 µs      3.70M
   pb-small-10   ==     seq     175      752      1785     91.04 µs      8.26M
   pb-small-10   ==    tree      53      291       748     56.70 µs      5.13M
   pb-small-10   ==   radix     103      364       830     96.12 µs      3.79M
   pb-small-10   ==    wdog     128      348       797     77.04 µs      4.52M
   pb-small-10   ==  wdog-l    1083     2753      6437    603.10 µs      4.56M
   pb-large-10   <=   adder      65      435      1531     14.70 µs     29.59M
   pb-large-10   <= diagram      29       86       198     25.79 µs      3.33M
   pb-large-10   <=     seq    7326    18561     41836      1.48 ms     12.52M
   pb-large-10   <=    tree     228      497      1206    106.80 µs      4.65M
   pb-large-10   <=   radix     327     1062      2446    280.70 µs      3.78M
   pb-large-10   <=    wdog     168      484      1158    100.00 µs      4.84M
   pb-large-10   <=  wdog-l    1525     4264     10213    854.10 µs      4.99M
   pb-large-10   ==   adder      55      399      1362     13.91 µs     28.68M
   pb-large-10   == diagram      14       61       133     25.87 µs      2.36M
   pb-large-10   ==     seq    4848    18949     44941      1.91 ms      9.92M
   pb-large-10   ==    tree     228      763      1963    198.50 µs      3.84M
   pb-large-10   ==   radix     327     1068      2440    278.90 µs      3.83M
   pb-large-10   ==    wdog     355     1037      2471    204.50 µs      5.07M
   pb-large-10   ==  wdog-l    3103     8701     20837      1.70 ms      5.12M
  pb-coprime-8   <=   adder      37      238       823      8.46 µs     28.14M
  pb-coprime-8   <= diagram      21       66       150     19.12 µs      3.45M
  pb-coprime-8   <=     seq     294      733      1646     68.29 µs     10.73M
  pb-coprime-8   <=    tree      36       76       169     14.66 µs      5.18M
  pb-coprime-8   <=   radix     181      571      1296    158.50 µs      3.60M
  pb-coprime-8   <=    wdog      90      248       587     52.66 µs      4.71M
  pb-coprime-8   <=  wdog-l     567     1548      3684    307.40 µs      5.04M
  pb-coprime-8   ==   adder      31      219       742      8.04 µs     27.24M
  pb-coprime-8   == diagram      18       81       184     25.29 µs      3.20M
  pb-coprime-8   ==     seq     175      652      1536     82.49 µs      7.90M
  pb-coprime-8   ==    tree      36      121       280     23.83 µs      5.08M
  pb-coprime-8   ==   radix     181      574      1293    155.90 µs      3.68M
  pb-coprime-8   ==    wdog     193      546      1284    110.30 µs      4.95M
  pb-coprime-8   ==  wdog-l    1172     3204      7614    640.90 µs      5.00M
    pb-wide-40   <=   adder      92      635      2251     21.20 µs     29.95M
    pb-wide-40   <= diagram     550     1650      3836    279.10 µs      5.91M
    pb-wide-40   <=     seq    2067     6027     13961    534.10 µs     11.28M
    pb-wide-40   <=    tree     272     1845      5020    290.50 µs      6.35M
    pb-wide-40   <=   radix     369     1702      4133    343.70 µs      4.95M
    pb-wide-40   <=    wdog     269     1202      3095    192.20 µs      6.25M
    pb-wide-40   <=  wdog-l   11085    50410    131205      7.46 ms      6.75M
    pb-wide-40   ==   adder      87      621      2180     20.54 µs     30.23M
    pb-wide-40   == diagram     563     2775      6622    467.30 µs      5.94M
    pb-wide-40   ==     seq    1490     7170     17158    745.70 µs      9.62M
    pb-wide-40   ==    tree     272     3414      9509    530.90 µs      6.43M
    pb-wide-40   ==   radix     369     1705      4135    348.20 µs      4.90M
    pb-wide-40   ==    wdog     581     2599      6609    400.70 µs      6.49M
    pb-wide-40   ==  wdog-l   22256   101727    264868     14.93 ms      6.81M
       amo-6x4   <=   adder      78      536      1893     17.74 µs     30.21M
       amo-6x4   <= diagram      44      177       441     34.83 µs      5.08M
       amo-6x4   <=     seq     170      644      1601     66.70 µs      9.66M
       amo-6x4   <=    tree      54      197       495     27.29 µs      7.22M
       amo-6x4   <=   radix     179      667      1556    160.00 µs      4.17M
       amo-6x4   <=    wdog     109      319       751     55.74 µs      5.72M
       amo-6x4   <=  wdog-l    2096     5763     13502      1.01 ms      5.72M
       amo-6x4   ==   adder      72      515      1799     17.29 µs     29.79M
       amo-6x4   == diagram      42      308       780     57.04 µs      5.40M
       amo-6x4   ==     seq     106      717      1864     95.87 µs      7.48M
       amo-6x4   ==    tree      54      345       891     51.29 µs      6.73M
       amo-6x4   ==   radix     179      670      1552    157.20 µs      4.26M
       amo-6x4   ==    wdog     255      748      1732    119.20 µs      6.28M
       amo-6x4   ==  wdog-l    4253    11697     27372      2.01 ms      5.83M
      int-6x40   <=   adder      92      413      1445     14.91 µs     27.70M
      int-6x40   <= diagram     600    10669     30938      1.52 ms      7.01M
      int-6x40   <=     seq     840    17629     51178      2.07 ms      8.53M
      int-6x40   <=    tree     600    11490     33360      1.50 ms      7.65M
      int-6x40   <=   radix     694     2087      4873    341.20 µs      6.12M
      int-6x40   <=    wdog     428     6000     12426    205.90 µs     29.14M
      int-6x40   <=  wdog-l   39906   221346    481626     25.23 ms      8.77M
      int-6x40   ==   adder      85      386      1314     14.04 µs     27.49M
      int-6x40   == diagram     600    20749     60698      2.93 ms      7.08M
      int-6x40   ==     seq     720    27430     80459      3.61 ms      7.60M
      int-6x40   ==    tree     600    22311     65421      2.79 ms      7.99M
      int-6x40   ==   radix     694     2091      4865    344.60 µs      6.07M
      int-6x40   ==    wdog    1096     8760     18606    425.30 µs     20.60M
      int-6x40   ==  wdog-l   80052   439452    957006     51.15 ms      8.59M
         pb-n8   <=   adder      19      119       401      4.71 µs     25.28M
         pb-n8   <= diagram      13       44        97     15.20 µs      2.89M
         pb-n8   <=     seq      63      156       344     20.16 µs      7.74M
         pb-n8   <=    tree      21       50       109     12.12 µs      4.13M
         pb-n8   <=   radix      85      271       604     80.87 µs      3.35M
         pb-n8   <=    wdog      39      105       241     27.08 µs      3.88M
         pb-n8   <=  wdog-l     314      807      1889    180.30 µs      4.48M
         pb-n8   ==   adder      16      112       375      4.54 µs     24.67M
         pb-n8   == diagram      11       50       112     18.58 µs      2.69M
         pb-n8   ==     seq      54      214       502     31.87 µs      6.71M
         pb-n8   ==    tree      21       80       182     18.29 µs      4.37M
         pb-n8   ==   radix      85      273       604     78.91 µs      3.46M
         pb-n8   ==    wdog      90      256       585     55.12 µs      4.64M
         pb-n8   ==  wdog-l     650     1693      3954    358.10 µs      4.73M
        pb-n16   <=   adder      42      285       998     10.04 µs     28.39M
        pb-n16   <= diagram     122      366       847     72.54 µs      5.05M
        pb-n16   <=     seq     495     1365      3123    129.10 µs     10.57M
        pb-n16   <=    tree     100      303       724     50.83 µs      5.96M
        pb-n16   <=   radix     186      711      1662    165.00 µs      4.31M
        pb-n16   <=    wdog     110      355       858     70.83 µs      5.01M
        pb-n16   <=  wdog-l    1818     5746     14063      1.01 ms      5.66M
        pb-n16   ==   adder      37      266       916      9.12 µs     29.15M
        pb-n16   == diagram     123      602      1429    116.90 µs      5.15M
        pb-n16   ==     seq     362     1621      3861    188.40 µs      8.60M
        pb-n16   ==    tree     100      510      1267     88.74 µs      5.75M
        pb-n16   ==   radix     186      713      1662    166.00 µs      4.30M
        pb-n16   ==    wdog     240      794      1902    146.90 µs      5.41M
        pb-n16   ==  wdog-l    3661    11602     28373      2.05 ms      5.67M
        pb-n32   <=   adder      96      649      2287     21.91 µs     29.62M
        pb-n32   <= diagram     712     2130      4960    343.20 µs      6.21M
        pb-n32   <=     seq    2139     6172     14276    544.10 µs     11.34M
        pb-n32   <=    tree     267     1435      3812    233.20 µs      6.15M
        pb-n32   <=   radix     452     1970      4742    418.70 µs      4.71M
        pb-n32   <=    wdog     271     1172      2998    189.60 µs      6.18M
        pb-n32   <=  wdog-l    9280    39800    102620      5.92 ms      6.72M
        pb-n32   ==   adder      90      630      2208     20.99 µs     30.01M
        pb-n32   == diagram     716     3559      8516    588.40 µs      6.05M
        pb-n32   ==     seq    1629     7762     18572    813.20 µs      9.55M
        pb-n32   ==    tree     267     2602      7115    410.30 µs      6.34M
        pb-n32   ==   radix     452     1974      4745    425.90 µs      4.63M
        pb-n32   ==    wdog     577     2503      6341    394.60 µs      6.34M
        pb-n32   ==  wdog-l   18428    79828    206040     11.87 ms      6.73M
        pb-n64   <=   adder     190     1294      4578     41.54 µs     31.15M
        pb-n64   <= diagram    3049     9135     21298      1.30 ms      7.03M
        pb-n64   <=     seq    8631    25404     59024      2.10 ms     12.11M
        pb-n64   <=    tree     701     8693     24746      1.43 ms      6.07M
        pb-n64   <=   radix     892     4443     11004    856.60 µs      5.19M
        pb-n64   <=    wdog     615     3555      9487    523.00 µs      6.80M
        pb-n64   <=  wdog-l   41052   242264    651364     33.02 ms      7.34M
        pb-n64   ==   adder     183     1274      4500     40.99 µs     31.08M
        pb-n64   == diagram    3061    15267     36592      2.23 ms      6.85M
        pb-n64   ==     seq    6658    32523     77944      3.05 ms     10.65M
        pb-n64   ==    tree     701    16640     48070      2.64 ms      6.31M
        pb-n64   ==   radix     892     4446     11005    843.70 µs      5.27M
        pb-n64   ==    wdog    1298     7433     19681      1.03 ms      7.24M
        pb-n64   ==  wdog-l   82254   486534   1308234     68.05 ms      7.15M
        pb-k11   <=   adder      12       79       268      3.46 µs     22.85M
        pb-k11   <= diagram      13       40        89     14.95 µs      2.68M
        pb-k11   <=     seq      77      191       423     22.66 µs      8.43M
        pb-k11   <=    tree      23       55       122     12.95 µs      4.25M
        pb-k11   <=   radix      64      194       430     64.45 µs      3.01M
        pb-k11   <=    wdog      23       59       132     18.74 µs      3.15M
        pb-k11   <=  wdog-l     220      540      1252    135.00 µs      4.00M
        pb-k11   ==   adder      10       75       244      3.33 µs     22.51M
        pb-k11   == diagram      12       53       120     20.29 µs      2.61M
        pb-k11   ==     seq      69      277       652     40.04 µs      6.92M
        pb-k11   ==    tree      23       88       203     20.33 µs      4.33M
        pb-k11   ==   radix      64      197       432     63.45 µs      3.10M
        pb-k11   ==    wdog      63      170       378     43.16 µs      3.94M
        pb-k11   ==  wdog-l     454     1104      2542    273.80 µs      4.03M
       pb-k131   <=   adder      36      249       874      8.96 µs     27.80M
       pb-k131   <= diagram      19       59       134     18.16 µs      3.25M
       pb-k131   <=     seq     917     2295      5175    193.90 µs     11.84M
       pb-k131   <=    tree      39       80       179     15.12 µs      5.29M
       pb-k131   <=   radix     164      512      1159    143.70 µs      3.56M
       pb-k131   <=    wdog      91      281       676     56.74 µs      4.95M
       pb-k131   <=  wdog-l     684     1955      4692    376.70 µs      5.19M
       pb-k131   ==   adder      30      225       760      8.37 µs     26.87M
       pb-k131   == diagram       3       16        28     11.70 µs      1.37M
       pb-k131   ==     seq     593     2258      5342    254.40 µs      8.88M
       pb-k131   ==    tree      39      124       287     25.20 µs      4.92M
       pb-k131   ==   radix     164      517      1158    144.40 µs      3.58M
       pb-k131   ==    wdog     190      587      1395    118.70 µs      4.95M
       pb-k131   ==  wdog-l    1390     3978      9535    774.80 µs      5.13M
       pb-k963   <=   adder      51      337      1186     12.12 µs     27.81M
       pb-k963   <= diagram      16       46       106     16.29 µs      2.82M
       pb-k963   <=     seq    6741    17271     39287      1.32 ms     13.07M
       pb-k963   <=    tree      41       81       183     14.66 µs      5.53M
       pb-k963   <=   radix     283      890      2019    236.10 µs      3.77M
       pb-k963   <=    wdog     131      389       940     76.12 µs      5.11M
       pb-k963   <=  wdog-l     901     2516      6015    497.30 µs      5.06M
       pb-k963   ==   adder      43      310      1048     11.12 µs     27.88M
       pb-k963   == diagram       0        8         8      7.92 µs      1.01M
       pb-k963   ==     seq    4572    18313     43490      1.80 ms     10.16M
       pb-k963   ==    tree      41      127       295     24.54 µs      5.18M
       pb-k963   ==   radix     283      894      2012    233.40 µs      3.83M
       pb-k963   ==    wdog     262      788      1886    156.70 µs      5.03M
       pb-k963   ==  wdog-l    1828     5122     12239      1.02 ms      5.00M
      pb-k8131   <=   adder      71      483      1722     16.24 µs     29.74M
      pb-k8131   <= diagram      16       50       113     16.16 µs      3.09M
      pb-k8131   <=     seq   56917   142199    320887     10.84 ms     13.12M
      pb-k8131   <=    tree      39       79       177     14.99 µs      5.27M
      pb-k8131   <=   radix     422     1348      3109    361.50 µs      3.73M
      pb-k8131   <=    wdog     189      552      1325    108.40 µs      5.09M
      pb-k8131   <=  wdog-l    1340     3702      8835    735.10 µs      5.04M
      pb-k8131   ==   adder      60      443      1502     15.33 µs     28.90M
      pb-k8131   == diagram       0        8         8      8.29 µs      0.96M
      pb-k8131   ==     seq   44417   176578    419230     16.99 ms     10.39M
      pb-k8131   ==    tree      39      124       287     24.41 µs      5.08M
      pb-k8131   ==   radix     422     1355      3095    357.70 µs      3.79M
      pb-k8131   ==    wdog     386     1136      2714    217.60 µs      5.22M
      pb-k8131   ==  wdog-l    2714     7502     17895      1.47 ms      5.12M
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
