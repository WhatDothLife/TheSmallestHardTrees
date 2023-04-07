Tripolys
====================================

A program for checking homomorphisms and testing polymorphism conditions of
directed graphs. Also implements an algorithm to generate orientations of trees,
and core orientations of trees. 

This repository contains companion code for the following paper. The results  be
found in a separate data repository over
[here](https://github.com/WhatDothLife/HardTreesData). The python code can be
found [here](https://github.com/Zerwas/TheSmallestHardTreesPython).  If you use
this code, please cite the paper. You can use the bibtex reference below. (TODO
update once published)

_M. Bodirsky, J. Bulín, F. Starke, and M. Wernthaler. The smallest hard trees, arXiv:2205.07528 [math.RA] (May 2022)_
https://doi.org/10.48550/arXiv.2205.07528
 
```
@misc{https://doi.org/10.1007/s10601-023-09341-8,
  doi = {10.1007/s10601-023-09341-8},
  url = {https://link.springer.com/article/10.1007/s10601-023-09341-8},
  author = {Bodirsky, Manuel and Bulín, Jakub and Starke, Florian and Wernthaler, Michael},  
  keywords = {Rings and Algebras (math.RA), FOS: Mathematics, FOS: Mathematics, G.2.2, 08A70, 08B05},  
  title = {The Smallest Hard Trees},
  publisher = {springer},
  year = {2023},
  copyright = {Creative Commons Attribution Non Commercial Share Alike 4.0 International}
}
```

Introduction
-----------------
In the paper *The Smallest Hard Trees*, we study computational and descriptive
complexity of fixed-template CSPs for small orientations of trees. The paper
contains a number of experimental results (see Section 7). Below you can find
the commands to reproduce those results. The commands assume that the data
repository has been cloned to `data/`.

Installation
-----------------
The Rust code is compatible with Rust 2021.

```
git clone https://gitlab.com/WhatDothLife/TheSmallestHardTrees.git
cd TheSmallestHardTrees
cargo build --release
```
The executable can be found in `./target/release/tripolys`.


Usage
-----------------

### Generate small trees and core trees
In Section 4, we introduce algorithms to generate small trees and core trees.
The numbers of such trees are given in Table 2 in Section 7.

- Generate all trees with number of vertices between `n` and `m`:
```
tripolys generate -s n -e m
```

- Generate all core trees with number of vertices between `n` and `m`:
  
```
tripolys generate -s n -e m --core
```

You may need to modify the path to the data folder via the option `data_path`
[default value: `./data`]. 

### The smallest NP-hard trees (Section 7.1.1) 

The trees can be found
[here](https://github.com/WhatDothLife/HardTreesData/blob/master/20/core_trees_kmm_deny.csv).
To reproduce the result, run the following sequence of commands:

```
cd data/20
tripolys polymorphism -i core_trees.edges -o core_trees_2-wnu_deny.csv -c 2-wnu -f deny
tripolys polymorphism -i core_trees_2-wnu_deny.csv -o core_trees_kmm_deny.csv -c kmm -f deny
```

We also found the smallest NP-hard triads: 
The triads can be found [here](https://github.com/WhatDothLife/HardTreesData/blob/master/22/core_triads_kmm_deny.csv).

```
tripolys generate -s 4 -e 22 --core --triad
```

```
cd data/22
tripolys polymorphism -i core_triads.edges -o core_triads_2-wnu_deny.csv -c 2-wnu -f deny
tripolys polymorphism -i core_triads_2-wnu_deny.csv -o core_triads_kmm_deny.csv -c kmm -f deny
```

Or test each one with it's compact encoding:

```
tripolys polymorphism -g 10110000,0101111,100111 -c kmm
tripolys polymorphism -g 10110000,1001111,010111 -c kmm
```


### The smallest NL-hard trees (Section 7.1.2)

```
cd data/12
tripolys polymorphism -i core_trees.edges -o core_trees_8-hami_deny.csv -c 8-hami -f deny
```

### The smallest tree not solved by Datalog (Section 7.1.3)

TODO

### The smallest tree not solved by Arc Consistency (Section 7.1.4)

The trees not solved by Arc Consistency are
[here](https://github.com/WhatDothLife/HardTreesData/blob/master/19/core_trees_2-wnu_deny.csv)
and this is how you can test them:

```
cd data/19
tripolys polymorphism -i core_trees.edges -o core_trees_2-wnu_deny.csv -c 2-wnu -f deny
```


### A tree not known to be in NL (Section 7.2.1)

The trees not known to be in NL are
[here](https://github.com/WhatDothLife/HardTreesData/blob/master/16/core_trees_majority_deny.csv)
and this is how you can test them:

```
cd data/16
tripolys polymorphism -i core_trees.edges -o core_trees_majority_deny.csv -c majority -f deny
```

```
tripolys polymorphism -g '[(0,1),(0,5),(1,2),(2,3),(3,4),(5,11),(6,5),(6,8),(7,6),(8,9),(9,10),(12,11),(12,14),(13,12),(14,15)]' -c 2-homck
```

```
tripolys polymorphism -g '[(0,1),(0,5),(1,2),(2,3),(3,4),(5,11),(6,5),(6,8),(7,6),(8,9),(9,10),(12,11),(12,14),(13,12),(14,15)]' -c 5-kk
```

```
tripolys polymorphism -g '[(0,1),(0,5),(1,2),(2,3),(3,4),(5,11),(6,5),(6,8),(7,6),(8,9),(9,10),(12,11),(12,14),(13,12),(14,15)]' -c 1000-j
```

### Trees that might be P-hard (Section 7.2.2)

```
cd data/18
tripolys polymorphism -i core_trees.edges -o core_trees_5-kk_deny.csv -c 5-kk -f deny
```

```
tripolys polymorphism -i core_trees_5-kk_deny.csv -o core_trees_kk-1000.csv -c kk-1000
tripolys polymorphism -i core_trees_5-kk_deny.csv -o core_trees_homck-1000.csv -c homck-1000
```

Other usage examples
-----------------
Use `--help`
```
tripolys polymorphism -g 1011000,1001111,010111 -c kmm -I
```
```
tripolys polymorphism -g k3 -c 3-wnu -I
```
```
tripolys homomorphism --from p5 --to c2
```

Contact
-----------------
You can report issues and ask questions in the repository's issues page. 

License
-----------------
This program is released under the terms of the GNU General Public License v3.0.

Visit this [page](http://gnugpl.org/) for license details.
