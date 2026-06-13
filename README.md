Tripolys
====================================

Companion code for the paper *The Smallest Hard Trees*. Provides two command-line
tools for generating orientations of trees and testing polymorphism conditions of
directed graphs.

The experimental results can be found in a separate data repository
[here](https://github.com/WhatDothLife/HardTreesData). The Python code can be
found [here](https://github.com/Zerwas/TheSmallestHardTreesPython). If you use
this code, please cite the paper:

_M. Bodirsky, J. Bulín, F. Starke, and M. Wernthaler. The Smallest Hard Trees.
Constraints, Springer, 2023._
https://doi.org/10.1007/s10601-023-09341-8

```bibtex
@article{https://doi.org/10.1007/s10601-023-09341-8,
  doi = {10.1007/s10601-023-09341-8},
  url = {https://link.springer.com/article/10.1007/s10601-023-09341-8},
  author = {Bodirsky, Manuel and Bulín, Jakub and Starke, Florian and Wernthaler, Michael},
  title = {The Smallest Hard Trees},
  publisher = {Springer},
  year = {2023},
  copyright = {Creative Commons Attribution Non Commercial Share Alike 4.0 International}
}
```

Installation
-----------------
Requires Rust 2021 edition or later.

```
git clone https://github.com/WhatDothLife/TheSmallestHardTrees.git
cd TheSmallestHardTrees
cargo build --release
```

The two executables can be found in `./target/release/`.

Usage
-----------------

### `generate` — Generate orientations of trees

```
generate --start <NUM> --end <NUM> [OPTIONS]
```

Generate all orientations of trees with a given number of vertices. Results are
written as edge lists to the data directory (default: `./data`), one file per
vertex count.

**Options:**
- `-s`, `--start <NUM>` — start vertex count (required)
- `-e`, `--end <NUM>` — end vertex count, inclusive (required)
- `-c`, `--core` — only generate cores
- `-t`, `--triad` — only generate triads
- `-d`, `--data_path <PATH>` — data directory (default: `./data`)
- `-o`, `--output <FILE>` — write statistics to a CSV file
- `-n`, `--no-write` — do not write results to disk

**Examples:**

Generate all trees with 1 to 20 vertices:
```
generate -s 1 -e 20
```

Generate all core trees with 1 to 20 vertices:
```
generate -s 1 -e 20 --core
```

Generate all core triads with 4 to 22 vertices:
```
generate -s 4 -e 22 --core --triad
```

---

### `polymorphism` — Test polymorphism conditions

```
polymorphism --condition <NAME> [--graph <H> | --input <PATH> --output <PATH>] [OPTIONS]
```

Test whether a digraph admits polymorphisms satisfying a given condition.

**Modes:**
- `--graph <H>` — test a single graph, given as an inline edge list or a file containing one edge list
- `--input <PATH> --output <PATH>` — test every graph in a file (one edge list per line) and write results to a CSV

**Conditions** (pass name to `-c`):

| Name | Condition |
|------|-----------|
| `majority` | Majority |
| `k-nu` | k-ary near-unanimity |
| `k-wnu` | k-ary weak near-unanimity |
| `kmm` | Kearnes-Marković-McKenzie |
| `n-j` | Jónsson chain of length n |
| `n-kk` | Kearnes-Kiss chain of length n |
| `n-homck` | Hobby-McKenzie chain of length n |
| `n-hami` | Hagemann-Mitschke chain of length n |
| `n-ts` | Totally symmetric of arity n |
| `siggers` | Siggers |

Custom identities can also be passed directly, separated by `,`:
```
polymorphism -c 'p(xyy)=q(yxx)=q(xxy),p(xyx)=q(xyx)' -g '[(0,1),(1,2),(2,0)]'
```

**Examples:**

Test a single graph for a majority polymorphism:
```
polymorphism -c majority -g "[(0,1),(1,2),(2,0)]"
```

Test all core trees with 20 vertices for KMM polymorphisms, keep only those that deny:
```
polymorphism -c kmm -i data/20/core_trees.edges -o results.csv -f deny
```

---

Reproducing the Results
-----------------
The commands below reproduce the experimental results from Section 7 of the paper.
They assume that the data repository has been cloned to `data/`.

### The smallest NP-hard trees (Section 7.1.1)

The 36 NP-hard trees with 20 vertices are
[here](https://github.com/WhatDothLife/HardTreesData/blob/master/20/core_trees_kmm_deny.csv).

```
polymorphism -c 2-wnu -i data/20/core_trees.edges -o data/20/core_trees_2-wnu_deny.csv -f deny
polymorphism -c kmm   -i data/20/core_trees_2-wnu_deny.csv -o data/20/core_trees_kmm_deny.csv -f deny
```

The 4 smallest NP-hard triads with 22 vertices are
[here](https://github.com/WhatDothLife/HardTreesData/blob/master/22/core_triads_kmm_deny.csv).

```
polymorphism -c 2-wnu -i data/22/core_triads.edges -o data/22/core_triads_2-wnu_deny.csv -f deny
polymorphism -c kmm   -i data/22/core_triads_2-wnu_deny.csv -o data/22/core_triads_kmm_deny.csv -f deny
```

### The smallest NL-hard trees (Section 7.1.2)

```
polymorphism -c 8-hami -i data/12/core_trees.edges -o data/12/core_trees_8-hami_deny.csv -f deny
```

### The smallest tree not solved by Arc Consistency (Section 7.1.4)

```
polymorphism -c 2-wnu -i data/19/core_trees.edges -o data/19/core_trees_2-wnu_deny.csv -f deny
```

### Trees not known to be in NL (Section 7.2.1)

```
polymorphism -c majority -i data/16/core_trees.edges -o data/16/core_trees_majority_deny.csv -f deny
```

Test individual trees:
```
polymorphism -c 2-homck -g '[(0,1),(0,5),(1,2),(2,3),(3,4),(5,11),(6,5),(6,8),(7,6),(8,9),(9,10),(12,11),(12,14),(13,12),(14,15)]'
polymorphism -c 5-kk    -g '[(0,1),(0,5),(1,2),(2,3),(3,4),(5,11),(6,5),(6,8),(7,6),(8,9),(9,10),(12,11),(12,14),(13,12),(14,15)]'
```

### Trees that might be P-hard (Section 7.2.2)

```
polymorphism -c 5-kk -i data/18/core_trees.edges -o data/18/core_trees_5-kk_deny.csv -f deny
```

---

Contact
-----------------
You can report issues and ask questions in the repository's issues page.

License
-----------------
This program is released under the terms of the GNU General Public License v3.0.

Visit this [page](http://gnugpl.org/) for license details.
