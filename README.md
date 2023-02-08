Tripolys
====================================

A program for checking homomorphisms and testing polymorphism conditions of
directed graphs. Also implements an algorithm to generate orientations of trees,
and core orientations of trees. 

This repository contains companion code for the following paper. If you use this
code, please cite the paper. You can use the bibtex reference below. (TODO
update once published)

_M. Bodirsky, J. Bulín, F. Starke, and M. Wernthaler. The smallest hard trees, arXiv:2205.07528 [math.RA] (May 2022)_
https://doi.org/10.48550/arXiv.2205.07528
 
```
@misc{https://doi.org/10.48550/arxiv.2205.07528,
  doi = {10.48550/ARXIV.2205.07528},
  url = {https://arxiv.org/abs/2205.07528},
  author = {Bodirsky, Manuel and Bulín, Jakub and Starke, Florian and Wernthaler, Michael},  
  keywords = {Rings and Algebras (math.RA), FOS: Mathematics, FOS: Mathematics, G.2.2, 08A70, 08B05},  
  title = {The Smallest Hard Trees},
  publisher = {arXiv},
  year = {2022},
  copyright = {Creative Commons Attribution Non Commercial Share Alike 4.0 International}
}
```

Introduction
-----------------
In the paper *The Smallest Hard Trees*, we study computational and descriptive
complexity of fixed-template CSPs for small orientations of trees. The paper
contains a number of experimental results (see Section 7). Below you can find
the commands to reproduce those results. Edgelists of all trees with up to 20 vertices can be found [here](https://gitlab.com/WhatDothLife/tripolys_data/-/tree/master/).

Installation
-----------------
The Rust code is compatible with Rust 2021. The Python code is compatible with Python 3.7.

```
git clone https://gitlab.com/WhatDothLife/tripolys.git
cd tripolys
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

The trees can be found [here](file:data/20/kmm_deny.csv ). (TODO put the data there)
To reproduce the result, run the following sequence of commands:

```
cd data/20
tripolys polymorphism -i cores.edges -o 2-wnu_deny.csv -c 2-wnu -L -f deny
tripolys polymorphism -i 2-wnu_deny.csv -o 3-wnu_deny.csv -c 3-wnu -L -f deny
tripolys polymorphism -i 3-wnu_deny.csv -o kmm_deny.csv -c kmm -L -f deny
```

We also found the smallest NP-hard triads: (TODO link edge lists here?)
The triads can be found [here](file:data/20/triads/kmm_deny.csv ).

```
tripolys generate -s 4 -e 22 --core --triad
```

```
tripolys polymorphism -g 10110000,0101111,100111 -c kmm -L
tripolys polymorphism -g 10110000,1001111,010111 -c kmm -L
```


### The smallest NL-hard trees (Section 7.1.2)

TODO

### The smallest tree not solved by Datalog (Section 7.1.3)

TODO

### The smallest tree not solved by Arc Consistency (Section 7.1.4)

The trees not solved by Arc Consistency are
[TODO]
and this is how you can test them:

Using the Python code:
```
import treeGeneration
Ts = treeGeneration.getTreesFromFile('name of file with trees')
TsNoAC = [T for T in Ts if not treeGeneration.isTotallySymmetric(T)]
```


### A tree not known to be in NL (Section 7.2.1)

The trees not known to be in NL are
[here](https://gitlab.com/WhatDothLife/tripolys_data/-/blob/master/16/majority_deny.csv)
and this is how you can test them:

```
cd data/16
tripolys polymorphism -i cores.edges -o majority_deny.csv -c majority -L -f deny
```

(TODO how to run the tests for KK, HMcK, J?)

### Trees that might be P-hard (Section 7.2.2)

TODO

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
tripolys homomorphism -f graph -t t3
```
```
tripolys homomorphism -f p5 -t c2
```

Contact
-----------------
You can report issues and ask questions in the repository's issues page. 

License
-----------------
This program is released under the terms of the GNU General Public License v3.0.

Visit this [page](http://gnugpl.org/) for license details.
