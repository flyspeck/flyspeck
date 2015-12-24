archive_all.ml contains the master list of tame graphs that is used in the HOL Light flyspeck formalization.
Each graph carries a hash code for identification.

Tri.ML, Quad.ML, Pent.ML, Hex.ML are copies of the graph archive in the Isabelle tame graphs classification project.
The Isabelle program uses these files to define what the archive is and then checks that each generated graph
appears in this list.

string_archive.txt is the list of graphs in a raw text format that is generated from the informal Java graph generation program.

make_archive.hl  compares these different files to check compatibility.
