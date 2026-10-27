# Encoding baseline

What every encoder costs to run, and what it emits, over the shapes in
`encoding.rs`. Regenerate both halves with:

```
cargo bench -p pindakaas --bench encoding                    # timings
PINDAKAAS_SIZES=1 cargo bench -p pindakaas --bench encoding  # sizes
```

Taken on an Apple M4, rustc 1.98.1, `--release`. Absolute times move with the
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
       card-10   <=   adder      14       93       323      3.67 µs     25.38M
       card-10   <= diagram      25       66       152      9.58 µs      6.89M
       card-10   <=     seq      45      126       284      6.71 µs     18.79M
       card-10   <=    tree      23       69       161      5.58 µs     12.36M
       card-10   <=   radix      37      155       367     15.24 µs     10.17M
       card-10   <=    wdog      32       93       216      8.62 µs     10.78M
       card-10   <=  wdog-l     360      980      2320     70.66 µs     13.87M
       card-10   <=  wdog-s      29       69       168      8.37 µs      8.24M
       card-10   <=    sort      24       49       118      5.83 µs      8.40M
       card-10   ==   adder       8       72       254      3.17 µs     22.75M
       card-10   == diagram      25      116       272     12.95 µs      8.96M
       card-10   ==     seq      35      159       373     10.12 µs     15.71M
       card-10   ==    tree      23      118       284      8.41 µs     14.02M
       card-10   ==   radix      37      157       369     15.24 µs     10.30M
       card-10   ==    wdog      64      186       432     17.95 µs     10.36M
       card-10   ==  wdog-l     720     1960      4640    140.30 µs     13.97M
       card-10   ==  wdog-s      58      138       336     17.24 µs      8.00M
       card-10   ==    sort      24       98       236      7.58 µs     12.93M
       card-20   <=   adder      35      231       807      7.00 µs     33.00M
       card-20   <= diagram     100      281       652     23.45 µs     11.98M
       card-20   <=     seq     190      551      1264     16.62 µs     33.15M
       card-20   <=    tree      66      235       575     12.54 µs     18.74M
       card-20   <=   radix     107      484      1158     34.79 µs     13.91M
       card-20   <=    wdog      84      302       739     18.41 µs     16.40M
       card-20   <=  wdog-l    1900     6820     17060    302.90 µs     22.52M
       card-20   <=  wdog-s      78      233       601     18.37 µs     12.68M
       card-20   <=    sort      68      168       426     13.24 µs     12.69M
       card-20   ==   adder      25      198       704      6.46 µs     30.66M
       card-20   == diagram     100      481      1142     33.16 µs     14.51M
       card-20   ==     seq     145      689      1638     27.33 µs     25.21M
       card-20   ==    tree      66      411      1037     20.20 µs     20.35M
       card-20   ==   radix     107      486      1159     35.54 µs     13.67M
       card-20   ==    wdog     168      604      1478     35.33 µs     17.10M
       card-20   ==  wdog-l    3800    13640     34120    630.20 µs     21.64M
       card-20   ==  wdog-s     156      466      1202     38.58 µs     12.08M
       card-20   ==    sort      68      336       852     18.37 µs     18.29M
       card-40   <=   adder      75      505      1779     13.79 µs     36.62M
       card-40   <= diagram     400     1161      2702     64.45 µs     18.01M
       card-40   <=     seq     780     2301      5324     53.45 µs     43.05M
       card-40   <=    tree     172      784      2014     29.45 µs     26.62M
       card-40   <=   radix     225     1210      3003     63.12 µs     19.17M
       card-40   <=    wdog     208      985      2540     41.33 µs     23.83M
       card-40   <=  wdog-l    9360    46760    123160      1.54 ms     30.30M
       card-40   <=  wdog-s     196      806      2182     42.16 µs     19.12M
       card-40   <=    sort     176      576      1532     29.99 µs     19.21M
       card-40   ==   adder      62      464      1654     12.99 µs     35.72M
       card-40   == diagram     400     1961      4682     89.45 µs     21.92M
       card-40   ==     seq     590     2874      6868     81.70 µs     35.18M
       card-40   ==    tree     172     1411      3725     49.91 µs     28.27M
       card-40   ==   radix     225     1212      3004     63.58 µs     19.06M
       card-40   ==    wdog     416     1970      5080     87.24 µs     22.58M
       card-40   ==  wdog-l   18720    93520    246320      3.06 ms     30.56M
       card-40   ==  wdog-s     392     1612      4364     87.99 µs     18.32M
       card-40   ==    sort     176     1152      3064     44.79 µs     25.72M
       card-80   <=   adder     155     1059      3751     26.74 µs     39.60M
       card-80   <= diagram    1600     4721     11002    194.00 µs     24.34M
       card-80   <=     seq    3160     9401     21844    173.80 µs     54.09M
       card-80   <=    tree     424     2670      7176     73.58 µs     36.29M
       card-80   <=   radix     553     3300      8341    137.50 µs     24.00M
       card-80   <=    wdog     496     3331      9002    100.90 µs     33.01M
       card-80   <=  wdog-l   44240   328560    903600      8.15 ms     40.29M
       card-80   <=  wdog-s     472     2892      8124    104.00 µs     27.81M
       card-80   <=    sort     432     2032      5624     66.24 µs     30.68M
       card-80   ==   adder     139     1010      3604     25.87 µs     39.04M
       card-80   == diagram    1600     7921     18962    280.20 µs     28.27M
       card-80   ==     seq    2380    11744     28128    259.90 µs     45.19M
       card-80   ==    tree     424     4947     13589    131.40 µs     37.65M
       card-80   ==   radix     553     3301      8341    142.50 µs     23.16M
       card-80   ==    wdog     992     6662     18004    212.80 µs     31.31M
       card-80   ==  wdog-l   88480   657120   1807200     16.95 ms     38.77M
       card-80   ==  wdog-s     944     5784     16248    218.50 µs     26.47M
       card-80   ==    sort     432     4064     11248    116.70 µs     34.82M
   pb-small-10   <=   adder      23      153       532      3.58 µs     42.71M
   pb-small-10   <= diagram      29       81       186     10.95 µs      7.40M
   pb-small-10   <=     seq     198      521      1180     13.20 µs     39.47M
   pb-small-10   <=    tree      53      174       426     10.00 µs     17.40M
   pb-small-10   <=   radix      72      297       700     34.91 µs      8.51M
   pb-small-10   <=    wdog      54      141       326     15.04 µs      9.38M
   pb-small-10   <=  wdog-l     527     1323      3094    117.90 µs     11.22M
   pb-small-10   <=  wdog-s      49      106       258     14.12 µs      7.51M
   pb-small-10   ==   adder      10       97       328      2.58 µs     37.57M
   pb-small-10   == diagram      31      143       332     14.87 µs      9.62M
   pb-small-10   ==     seq     175      752      1785     21.58 µs     34.85M
   pb-small-10   ==    tree      53      291       748     14.91 µs     19.52M
   pb-small-10   ==   radix      72      299       699     34.95 µs      8.56M
   pb-small-10   ==    wdog     118      308       717     32.79 µs      9.39M
   pb-small-10   ==  wdog-l    1073     2713      6357    255.70 µs     10.61M
   pb-small-10   ==  wdog-s     109      235       577     30.91 µs      7.60M
   pb-large-10   <=   adder      65      435      1531      8.46 µs     51.44M
   pb-large-10   <= diagram      29       77       180     11.04 µs      6.97M
   pb-large-10   <=     seq    7326    18561     41836    241.40 µs     76.89M
   pb-large-10   <=    tree     228      497      1206     28.62 µs     17.37M
   pb-large-10   <=   radix     205      808      1921     97.29 µs      8.31M
   pb-large-10   <=    wdog     168      484      1158     34.70 µs     13.95M
   pb-large-10   <=  wdog-l    1525     4264     10213    319.80 µs     13.33M
   pb-large-10   <=  wdog-s     158      366       926     35.58 µs     10.29M
   pb-large-10   ==   adder      31      271       938      5.92 µs     45.82M
   pb-large-10   == diagram      14       60       130     12.33 µs      4.87M
   pb-large-10   ==     seq    4848    18949     44941    285.40 µs     66.39M
   pb-large-10   ==    tree     228      763      1963     45.49 µs     16.77M
   pb-large-10   ==   radix     205      814      1915     98.91 µs      8.23M
   pb-large-10   ==    wdog     345      997      2391     78.74 µs     12.66M
   pb-large-10   ==  wdog-l    3093     8661     20757    661.60 µs     13.09M
   pb-large-10   ==  wdog-s     324      756      1919     73.41 µs     10.30M
  pb-coprime-8   <=   adder      37      238       823      5.04 µs     47.22M
  pb-coprime-8   <= diagram      21       61       140      8.62 µs      7.07M
  pb-coprime-8   <=     seq     294      733      1646     14.91 µs     49.16M
  pb-coprime-8   <=    tree      36       76       169      5.96 µs     12.76M
  pb-coprime-8   <=   radix     118      439      1026     61.91 µs      7.09M
  pb-coprime-8   <=    wdog      90      248       587     20.99 µs     11.82M
  pb-coprime-8   <=  wdog-l     567     1548      3684    121.90 µs     12.70M
  pb-coprime-8   <=  wdog-s      81      190       479     19.24 µs      9.88M
  pb-coprime-8   ==   adder      20      174       610      3.83 µs     45.40M
  pb-coprime-8   == diagram      18       81       184     10.83 µs      7.48M
  pb-coprime-8   ==     seq     175      652      1536     18.54 µs     35.17M
  pb-coprime-8   ==    tree      36      121       279      8.75 µs     13.83M
  pb-coprime-8   ==   radix     118      442      1023     61.20 µs      7.22M
  pb-coprime-8   ==    wdog     185      514      1220     43.16 µs     11.91M
  pb-coprime-8   ==  wdog-l    1164     3172      7550    250.70 µs     12.65M
  pb-coprime-8   ==  wdog-s     169      395       998     40.66 µs      9.71M
    pb-wide-40   <=   adder      92      635      2251     11.58 µs     54.84M
    pb-wide-40   <= diagram     550     1625      3786     88.12 µs     18.44M
    pb-wide-40   <=     seq    2067     6027     13961    101.30 µs     59.50M
    pb-wide-40   <=    tree     272     1845      5020     63.12 µs     29.23M
    pb-wide-40   <=   radix     337     1627      3974    102.80 µs     15.83M
    pb-wide-40   <=    wdog     269     1202      3095     56.16 µs     21.40M
    pb-wide-40   <=  wdog-l   11085    50410    131205      2.04 ms     24.70M
    pb-wide-40   <=  wdog-s     261      994      2692     56.79 µs     17.50M
    pb-wide-40   ==   adder      83      606      2144     11.24 µs     53.91M
    pb-wide-40   == diagram     563     2775      6622    120.80 µs     22.97M
    pb-wide-40   ==     seq    1490     7170     17158    149.80 µs     47.86M
    pb-wide-40   ==    tree     272     3414      9509    102.20 µs     33.41M
    pb-wide-40   ==   radix     337     1630      3976    110.60 µs     14.74M
    pb-wide-40   ==    wdog     541     2439      6289    113.00 µs     21.58M
    pb-wide-40   ==  wdog-l   22216   101567    264548      4.14 ms     24.54M
    pb-wide-40   ==  wdog-s     527     2022      5481    119.60 µs     16.91M
       amo-6x4   <=   adder      81      556      1959     10.45 µs     53.21M
       amo-6x4   <= diagram      46      214       532     12.12 µs     17.66M
       amo-6x4   <=     seq     110      424      1049     10.54 µs     40.23M
       amo-6x4   <=    tree      53      223       568      9.17 µs     24.33M
       amo-6x4   <=   radix     114      433      1004     56.04 µs      7.73M
       amo-6x4   <=    wdog      82      227       524     17.91 µs     12.67M
       amo-6x4   <=  wdog-l    1379     3657      8567    277.20 µs     13.19M
       amo-6x4   <=  wdog-s      76      174       418     14.79 µs     11.76M
       amo-6x4   ==   adder      68      514      1816      9.75 µs     52.72M
       amo-6x4   == diagram      46      366       932     17.70 µs     20.68M
       amo-6x4   ==     seq      94      637      1656     17.95 µs     35.49M
       amo-6x4   ==    tree      53      393      1032     14.54 µs     27.03M
       amo-6x4   ==   radix     114      436      1003     56.54 µs      7.71M
       amo-6x4   ==    wdog     159      438      1012     34.91 µs     12.55M
       amo-6x4   ==  wdog-l    2630     6919     16196    540.40 µs     12.80M
       amo-6x4   ==  wdog-s     146      333       802     29.04 µs     11.47M
      int-6x40   <=   adder      92      413      1445      9.50 µs     43.48M
      int-6x40   <= diagram     600    10669     30938    267.30 µs     39.91M
      int-6x40   <=     seq     840    17629     51178    260.90 µs     67.57M
      int-6x40   <=    tree     600    11490     33360    168.70 µs     68.11M
      int-6x40   <=   radix     436     1361      3385    123.70 µs     11.00M
      int-6x40   <=    wdog     428     6000     12426     78.66 µs     76.28M
      int-6x40   <=  wdog-l   39906   221346    481626      8.92 ms     24.80M
      int-6x40   <=  wdog-s     423     5893     12212     81.83 µs     72.02M
      int-6x40   ==   adder      81      376      1292      8.92 µs     42.17M
      int-6x40   == diagram     600    20749     60698    431.90 µs     48.04M
      int-6x40   ==     seq     720    27430     80459    429.90 µs     63.81M
      int-6x40   ==    tree     600    22311     65421    328.70 µs     67.88M
      int-6x40   ==   radix     436     1365      3377    123.70 µs     11.03M
      int-6x40   ==    wdog     610     7074     14766    115.50 µs     61.25M
      int-6x40   ==  wdog-l   79566   437766    953166     18.09 ms     24.20M
      int-6x40   ==  wdog-s     600     6860     14338    103.80 µs     66.09M
         pb-n8   <=   adder      19      119       401      2.92 µs     40.81M
         pb-n8   <= diagram      13       38        85      7.37 µs      5.15M
         pb-n8   <=     seq      63      156       344      6.46 µs     24.16M
         pb-n8   <=    tree      21       50       109      5.25 µs      9.53M
         pb-n8   <=   radix      55      204       470     32.74 µs      6.23M
         pb-n8   <=    wdog      39      105       241     11.87 µs      8.85M
         pb-n8   <=  wdog-l     314      807      1889     73.87 µs     10.92M
         pb-n8   <=  wdog-s      39       82       195     11.99 µs      6.84M
         pb-n8   ==   adder       9       83       278      2.31 µs     35.90M
         pb-n8   == diagram      11       50       112      9.17 µs      5.45M
         pb-n8   ==     seq      54      214       502      9.96 µs     21.49M
         pb-n8   ==    tree      21       80       181      7.58 µs     10.55M
         pb-n8   ==   radix      55      206       470     32.83 µs      6.27M
         pb-n8   ==    wdog      82      224       521     23.74 µs      9.44M
         pb-n8   ==  wdog-l     642     1661      3890    150.20 µs     11.06M
         pb-n8   ==  wdog-s      80      169       411     24.12 µs      7.01M
        pb-n16   <=   adder      42      285       998      5.71 µs     49.94M
        pb-n16   <= diagram     122      358       831     25.74 µs     13.91M
        pb-n16   <=     seq     495     1365      3123     29.12 µs     46.88M
        pb-n16   <=    tree     100      303       724     16.12 µs     18.80M
        pb-n16   <=   radix     145      624      1486     57.04 µs     10.94M
        pb-n16   <=    wdog     110      355       858     25.62 µs     13.86M
        pb-n16   <=  wdog-l    1818     5746     14063    358.40 µs     16.03M
        pb-n16   <=  wdog-s     107      288       737     25.58 µs     11.26M
        pb-n16   ==   adder      31      246       864      5.08 µs     48.41M
        pb-n16   == diagram     123      602      1429     36.33 µs     16.57M
        pb-n16   ==     seq     362     1621      3861     40.45 µs     40.07M
        pb-n16   ==    tree     100      510      1266     23.95 µs     21.29M
        pb-n16   ==   radix     145      626      1486     56.41 µs     11.10M
        pb-n16   ==    wdog     224      730      1774     53.04 µs     13.76M
        pb-n16   ==  wdog-l    3645    11538     28245    721.80 µs     15.99M
        pb-n16   ==  wdog-s     215      583      1501     48.62 µs     11.99M
        pb-n32   <=   adder      96      649      2287     11.70 µs     55.47M
        pb-n32   <= diagram     712     2118      4936     99.49 µs     21.29M
        pb-n32   <=     seq    2139     6172     14276    102.60 µs     60.16M
        pb-n32   <=    tree     267     1435      3812     52.79 µs     27.18M
        pb-n32   <=   radix     373     1801      4395    128.40 µs     14.03M
        pb-n32   <=    wdog     271     1172      2998     55.83 µs     20.99M
        pb-n32   <=  wdog-l    9280    39800    102620      1.66 ms     23.92M
        pb-n32   <=  wdog-s     260      965      2602     56.49 µs     17.08M
        pb-n32   ==   adder      78      582      2064     10.83 µs     53.74M
        pb-n32   == diagram     716     3559      8516    143.00 µs     24.89M
        pb-n32   ==     seq    1629     7762     18572    145.10 µs     53.49M
        pb-n32   ==    tree     267     2602      7115     81.95 µs     31.75M
        pb-n32   ==   radix     373     1805      4398    128.20 µs     14.08M
        pb-n32   ==    wdog     545     2375      6085    111.80 µs     21.24M
        pb-n32   ==  wdog-l   18396    79700    205784      3.32 ms     24.01M
        pb-n32   ==  wdog-s     518     1932      5217    109.70 µs     17.61M
        pb-n64   <=   adder     190     1294      4578     22.16 µs     58.39M
        pb-n64   <= diagram    3049     9111     21250    349.50 µs     26.07M
        pb-n64   <=     seq    8631    25404     59024    365.90 µs     69.43M
        pb-n64   <=    tree     701     8693     24746    238.90 µs     36.39M
        pb-n64   <=   radix     759     4172     10460    239.70 µs     17.41M
        pb-n64   <=    wdog     615     3555      9487    126.30 µs     28.15M
        pb-n64   <=  wdog-l   41052   242264    651364      7.51 ms     32.27M
        pb-n64   <=  wdog-s     577     3045      8501    124.90 µs     24.38M
        pb-n64   ==   adder     169     1218      4324     21.12 µs     57.67M
        pb-n64   == diagram    3061    15267     36592    497.70 µs     30.68M
        pb-n64   ==     seq    6658    32523     77944    526.60 µs     61.76M
        pb-n64   ==    tree     701    16640     48070    390.90 µs     42.57M
        pb-n64   ==   radix     759     4175     10461    225.80 µs     18.49M
        pb-n64   ==    wdog    1234     7177     19169    256.60 µs     27.97M
        pb-n64   ==  wdog-l   82190   486278   1307722     15.64 ms     31.09M
        pb-n64   ==  wdog-s    1150     6106     17061    258.50 µs     23.62M
        pb-k11   <=   adder      12       79       268      2.21 µs     35.80M
        pb-k11   <= diagram      13       36        81      7.17 µs      5.02M
        pb-k11   <=     seq      77      191       423      6.92 µs     27.62M
        pb-k11   <=    tree      23       55       122      5.37 µs     10.23M
        pb-k11   <=   radix      38      139       320     25.95 µs      5.36M
        pb-k11   <=    wdog      23       59       132      9.08 µs      6.50M
        pb-k11   <=  wdog-l     220      540      1252     59.41 µs      9.09M
        pb-k11   <=  wdog-s      24       50       115      9.67 µs      5.17M
        pb-k11   ==   adder       3       49       168      1.52 µs     32.24M
        pb-k11   == diagram      12       53       120      9.54 µs      5.56M
        pb-k11   ==     seq      69      277       652     10.91 µs     25.39M
        pb-k11   ==    tree      23       88       202      7.67 µs     11.48M
        pb-k11   ==   radix      38      142       322     26.12 µs      5.44M
        pb-k11   ==    wdog      55      138       314     19.74 µs      6.99M
        pb-k11   ==  wdog-l     446     1072      2478    122.20 µs      8.77M
        pb-k11   ==  wdog-s      57      113       266     21.58 µs      5.24M
       pb-k131   <=   adder      36      249       874      5.21 µs     47.82M
       pb-k131   <= diagram      19       53       122      8.50 µs      6.24M
       pb-k131   <=     seq     917     2295      5175     36.62 µs     62.67M
       pb-k131   <=    tree      39       80       179      6.25 µs     12.80M
       pb-k131   <=   radix     100      378       885     58.33 µs      6.48M
       pb-k131   <=    wdog      91      281       676     21.99 µs     12.78M
       pb-k131   <=  wdog-l     684     1955      4692    133.70 µs     14.62M
       pb-k131   <=  wdog-s      96      236       597     22.49 µs     10.49M
       pb-k131   ==   adder      24      201       688      4.37 µs     45.95M
       pb-k131   == diagram       3       16        28      7.25 µs      2.21M
       pb-k131   ==     seq     593     2258      5342     43.45 µs     51.97M
       pb-k131   ==    tree      39      124       285      8.87 µs     13.97M
       pb-k131   ==   radix     100      383       884     55.49 µs      6.90M
       pb-k131   ==    wdog     182      555      1331     39.95 µs     13.89M
       pb-k131   ==  wdog-l    1382     3946      9471    285.60 µs     13.82M
       pb-k131   ==  wdog-s     186      449      1131     41.29 µs     10.87M
       pb-k963   <=   adder      51      337      1186      6.96 µs     48.44M
       pb-k963   <= diagram      16       40        94      7.71 µs      5.19M
       pb-k963   <=     seq    6741    17271     39287    215.80 µs     80.03M
       pb-k963   <=    tree      41       81       183      6.12 µs     13.23M
       pb-k963   <=   radix     177      671      1576     92.12 µs      7.28M
       pb-k963   <=    wdog     131      389       940     29.45 µs     13.21M
       pb-k963   <=  wdog-l     901     2516      6015    196.20 µs     12.82M
       pb-k963   <=  wdog-s     134      314       801     30.16 µs     10.41M
       pb-k963   ==   adder      31      261       901      5.46 µs     47.83M
       pb-k963   == diagram       0        8         8      5.75 µs      1.39M
       pb-k963   ==     seq    4572    18313     43490    264.70 µs     69.18M
       pb-k963   ==    tree      41      127       294      8.83 µs     14.38M
       pb-k963   ==   radix     177      675      1569     91.95 µs      7.34M
       pb-k963   ==    wdog     254      756      1822     59.08 µs     12.80M
       pb-k963   ==  wdog-l    1820     5090     12175    389.50 µs     13.07M
       pb-k963   ==  wdog-s     256      600      1523     56.91 µs     10.54M
      pb-k8131   <=   adder      71      483      1722      9.25 µs     52.22M
      pb-k8131   <= diagram      16       44       101      7.79 µs      5.65M
      pb-k8131   <=     seq   56917   142199    320887      1.65 ms     86.23M
      pb-k8131   <=    tree      39       79       177      6.08 µs     12.99M
      pb-k8131   <=   radix     266     1023      2428    143.40 µs      7.13M
      pb-k8131   <=    wdog     189      552      1325     41.16 µs     13.41M
      pb-k8131   <=  wdog-l    1340     3702      8835    283.40 µs     13.06M
      pb-k8131   <=  wdog-s     186      431      1094     41.62 µs     10.36M
      pb-k8131   ==   adder      42      360      1254      7.42 µs     48.54M
      pb-k8131   == diagram       0        8         8      5.92 µs      1.35M
      pb-k8131   ==     seq   44417   176578    419230      2.36 ms     74.73M
      pb-k8131   ==    tree      39      124       286      9.16 µs     13.53M
      pb-k8131   ==   radix     266     1030      2414    145.80 µs      7.06M
      pb-k8131   ==    wdog     378     1104      2650     83.95 µs     13.15M
      pb-k8131   ==  wdog-l    2706     7470     17831    573.60 µs     13.02M
      pb-k8131   ==  wdog-s     368      848      2151     82.70 µs     10.25M
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
   pigeonhole   adder     224     1254   >1048576  52880.9ms    unsat
   pigeonhole diagram     287      855      14025     95.9ms    unsat
   pigeonhole     seq     301      897      13401     89.3ms    unsat
   pigeonhole    tree     287      862      22251    132.5ms    unsat
   pigeonhole   radix     301     1198      82614    498.0ms    unsat
   pigeonhole    wdog     308      911      23552    142.7ms    unsat
   pigeonhole  wdog-l    5985    20280        t/o  90000.0ms      t/o
   pigeonhole  wdog-s     301      806     321291   2765.3ms    unsat
   pigeonhole    sort     287      771      56059    301.7ms    unsat
 market-split   adder     152     1000        356      1.7ms      sat
 market-split diagram    1316     6426        151      2.7ms      sat
 market-split     seq    6346    29314         16      1.3ms      sat
 market-split    tree     975    26808          1      0.3ms      sat
 market-split   radix     660     2852        176      1.7ms      sat
 market-split    wdog     961     3384       1060     12.4ms      sat
 market-split  wdog-l   18473    64903         68     11.7ms      sat
 market-split  wdog-s     907     2677        548      5.5ms      sat
     knapsack   adder     760     4785        t/o  90000.0ms      t/o
     knapsack diagram    2907    18369     122212   3885.4ms    unsat
     knapsack     seq    8454    50581     131556   4704.8ms    unsat
     knapsack    tree    2264    66163      88696   2158.2ms    unsat
     knapsack   radix    1161     4994     142491   2389.1ms    unsat
     knapsack    wdog    1148     4395        t/o  90000.0ms      t/o
     knapsack  wdog-l   65109   252483        t/o  90000.1ms      t/o
     knapsack  wdog-s    1098     3709        t/o  90000.0ms      t/o
      auction   adder     364     2691       1550     10.7ms    unsat
      auction diagram   29613    89137        178     29.9ms    unsat
      auction     seq  224251   653464        183    283.1ms    unsat
      auction    tree   11297  4204016        228    788.7ms    unsat
      auction   radix    1508     7729        329      4.3ms    unsat
      auction    wdog    1142     6521        228      2.8ms    unsat
      auction  wdog-l   43250   236130        199     72.9ms    unsat
      auction  wdog-s    1065     5550        227      2.6ms    unsat
```
