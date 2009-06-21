#include <fstream>
#include <iostream>
#include <list>
#include <vector>
#include <conio.h>
using namespace std;

list< list< list <int> > > bigBigList;
//ifstream fin("stripped_kepler.out");
ifstream fin("keplergraph_fixedhash.out");
ofstream fout;
//ofstream fbatch;
vector<string> hashCodeList;

void inputData() {
     bigBigList.clear();
     list< list<int> > bigList;
     hashCodeList.clear();
     
     while (!fin.eof()) {
         bigList.clear();
         
         string hashCode;
         int numFaces;
         
         fin >> hashCode; if ( fin.eof() ) break;
         hashCodeList.push_back(hashCode);
         
         fin >> numFaces;
         for (int i=0; i<numFaces; i++) {
             int numVertices;
             fin >> numVertices;
             
             list<int> subList;
             subList.clear();
             
             for (int j=0; j<numVertices; j++) {
                 int ver;
                 fin >> ver;
                 subList.push_back(ver);
             }
             
             bigList.push_back(subList);
         }
         
         bigBigList.push_back(bigList);
     }
}

void genGraphData() {
     //fbatch.open("GraphDat/batch_eol.bat");
     //fbatch << "echo off" << endl;
     
     list< list< list<int> > >::iterator it3;
     list< list<int> >::iterator it2;
     list<int>::iterator it1;
     string s, sbat1, sbat2;
     int tt;
     int count;
     int maxVer;
     vector<int> oneface;
     
     tt = 0;
     cout << bigBigList.size() << endl;
     for (it3 = bigBigList.begin(); it3 != bigBigList.end(); it3++) {
         s = "GraphDat/graph" + hashCodeList[tt] + ".dat";
         sbat1 = "graph" + hashCodeList[tt] + ".dat";
         sbat2 = "Unix/graph" + hashCodeList[tt] + ".dat";
         fout.open( s.c_str() );
         //fbatch << "eol Unix " << sbat1 << " " << sbat2 << endl;
         maxVer = 0;
         
         // Find CVERTEX
         for (it2 = (*it3).begin(); it2 != (*it3).end(); it2++) {
             for (it1 = (*it2).begin(); it1 != (*it2).end(); it1++) {
                 if (maxVer < *it1) maxVer = *it1;
             }
         }
         
         fout << "param CVERTEX := " << maxVer + 1 << ";" << endl;
         fout << "param CFACE := " << (*it3).size() << ";" << endl << endl;
         fout << "set EDART :=" << endl;
         
         count = 1;
         for (it2 = (*it3).begin(); it2 != (*it3).end(); it2++) {
             oneface.clear();
             for (it1 = (*it2).begin(); it1 != (*it2).end(); it1++) {
                 oneface.push_back((*it1) + 1);
             }
             
             // Print the EDARTs
             fout << " (*,*,*," << count << ")";
             for (int i = 0; i < oneface.size(); i++) {
                 fout << " " << oneface[i % oneface.size()] << " " << oneface[(i+1) % oneface.size()] << " " << oneface[(i+2) % oneface.size()];
                 if (i < oneface.size() - 1) fout << ",";
             }
             fout << endl;
             count++;
         }
         fout << ";" << endl;
         fout.close();
         tt++;
     }
     
     //fbatch.close();
}

int main() {
    inputData();
    genGraphData();
    
    cout << "Finish!" << endl;
    getch();
    return 0;
}
