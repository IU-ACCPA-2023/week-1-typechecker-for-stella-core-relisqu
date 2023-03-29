// Generated from stella/stellaParser.g4 by ANTLR 4.12.0
// jshint ignore: start
import antlr4 from 'antlr4';
import stellaParserListener from './stellaParserListener.js';
const serializedATN = [4,1,67,747,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,
4,2,5,7,5,2,6,7,6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,
2,13,7,13,2,14,7,14,2,15,7,15,2,16,7,16,2,17,7,17,2,18,7,18,2,19,7,19,2,
20,7,20,2,21,7,21,2,22,7,22,2,23,7,23,2,24,7,24,2,25,7,25,2,26,7,26,2,27,
7,27,2,28,7,28,2,29,7,29,2,30,7,30,2,31,7,31,2,32,7,32,2,33,7,33,2,34,7,
34,2,35,7,35,2,36,7,36,2,37,7,37,2,38,7,38,2,39,7,39,2,40,7,40,2,41,7,41,
2,42,7,42,2,43,7,43,2,44,7,44,2,45,7,45,2,46,7,46,2,47,7,47,2,48,7,48,2,
49,7,49,2,50,7,50,2,51,7,51,2,52,7,52,2,53,7,53,2,54,7,54,2,55,7,55,2,56,
7,56,2,57,7,57,2,58,7,58,2,59,7,59,2,60,7,60,2,61,7,61,2,62,7,62,2,63,7,
63,2,64,7,64,2,65,7,65,2,66,7,66,2,67,7,67,2,68,7,68,2,69,7,69,2,70,7,70,
2,71,7,71,2,72,7,72,2,73,7,73,2,74,7,74,2,75,7,75,1,0,1,0,1,0,1,1,1,1,1,
1,1,2,1,2,1,2,1,3,1,3,1,3,1,4,1,4,1,4,1,5,1,5,1,5,1,6,1,6,1,6,1,7,1,7,1,
7,1,8,1,8,1,8,1,9,1,9,1,9,1,10,1,10,1,10,1,11,1,11,1,11,1,12,1,12,1,12,1,
13,1,13,1,13,1,14,1,14,1,14,1,15,1,15,1,15,1,16,1,16,1,16,1,17,1,17,1,17,
1,18,1,18,1,18,1,19,1,19,1,19,1,20,1,20,1,20,1,21,1,21,1,21,1,22,1,22,1,
22,1,23,1,23,1,23,1,24,1,24,1,24,1,25,1,25,1,25,1,26,1,26,1,26,1,27,1,27,
1,27,1,28,1,28,1,28,1,29,1,29,1,29,1,30,1,30,1,30,1,31,1,31,1,31,1,32,1,
32,1,32,1,33,1,33,1,33,1,34,1,34,1,34,1,35,1,35,1,35,1,36,1,36,1,36,1,37,
1,37,1,37,1,38,1,38,1,38,1,38,1,39,1,39,1,39,1,39,1,40,1,40,1,40,1,40,1,
41,1,41,1,41,1,41,1,41,3,41,284,8,41,1,42,1,42,1,42,1,42,1,42,5,42,291,8,
42,10,42,12,42,294,9,42,1,43,1,43,1,43,1,43,1,43,1,43,1,43,1,43,1,43,1,43,
1,43,1,43,1,43,1,43,1,43,1,43,1,43,1,43,1,43,3,43,315,8,43,1,44,1,44,1,44,
5,44,320,8,44,10,44,12,44,323,9,44,1,45,1,45,1,46,1,46,1,46,1,46,1,46,5,
46,332,8,46,10,46,12,46,335,9,46,1,47,1,47,1,48,1,48,1,48,5,48,342,8,48,
10,48,12,48,345,9,48,1,49,1,49,1,49,1,49,1,50,1,50,1,50,1,50,1,50,1,50,3,
50,357,8,50,1,51,1,51,1,51,3,51,362,8,51,1,52,1,52,1,52,3,52,367,8,52,1,
53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,1,53,
3,53,384,8,53,1,54,1,54,1,54,1,54,1,54,1,54,3,54,392,8,54,1,55,1,55,1,55,
1,55,1,56,1,56,1,56,1,56,1,56,1,56,3,56,404,8,56,1,57,1,57,1,57,1,57,1,57,
1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,
57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,1,57,
1,57,1,57,1,57,1,57,1,57,3,57,445,8,57,1,58,1,58,1,58,1,58,1,58,1,58,3,58,
453,8,58,1,59,1,59,1,59,1,59,1,60,1,60,1,60,1,60,1,60,1,60,3,60,465,8,60,
1,61,1,61,1,61,1,61,1,62,1,62,1,62,1,62,1,62,1,62,3,62,477,8,62,1,63,1,63,
1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,1,
63,1,63,1,63,1,63,1,63,1,63,1,63,1,63,3,63,503,8,63,1,64,1,64,1,64,1,64,
1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,
64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,
1,64,1,64,1,64,1,64,3,64,542,8,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,1,64,
1,64,5,64,553,8,64,10,64,12,64,556,9,64,1,65,1,65,1,65,1,65,1,65,1,65,1,
65,1,65,1,65,5,65,567,8,65,10,65,12,65,570,9,65,1,66,1,66,1,66,1,66,1,66,
1,66,1,66,1,66,5,66,580,8,66,10,66,12,66,583,9,66,1,67,1,67,1,67,1,67,1,
67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,
1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,
67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,
1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,67,1,
67,1,67,1,67,1,67,1,67,1,67,1,67,3,67,654,8,67,1,68,1,68,1,68,1,68,1,68,
1,68,1,68,1,68,1,68,3,68,665,8,68,1,68,1,68,1,68,1,68,1,68,1,68,5,68,673,
8,68,10,68,12,68,676,9,68,1,69,1,69,1,69,1,69,1,69,1,69,1,69,1,69,1,69,1,
69,1,69,1,69,3,69,690,8,69,1,70,1,70,1,70,1,70,1,70,1,70,1,70,1,70,1,70,
1,70,1,70,1,70,1,70,1,70,1,70,1,70,1,70,1,70,1,70,3,70,711,8,70,1,71,1,71,
1,71,1,71,1,71,1,71,1,71,1,71,3,71,721,8,71,1,72,1,72,1,72,1,72,1,72,1,72,
3,72,729,8,72,1,73,1,73,1,73,1,73,1,74,1,74,1,74,1,74,1,74,1,74,3,74,741,
8,74,1,75,1,75,1,75,1,75,1,75,0,8,84,88,92,96,128,130,132,136,76,0,2,4,6,
8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,
58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,
106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140,
142,144,146,148,150,0,0,752,0,152,1,0,0,0,2,155,1,0,0,0,4,158,1,0,0,0,6,
161,1,0,0,0,8,164,1,0,0,0,10,167,1,0,0,0,12,170,1,0,0,0,14,173,1,0,0,0,16,
176,1,0,0,0,18,179,1,0,0,0,20,182,1,0,0,0,22,185,1,0,0,0,24,188,1,0,0,0,
26,191,1,0,0,0,28,194,1,0,0,0,30,197,1,0,0,0,32,200,1,0,0,0,34,203,1,0,0,
0,36,206,1,0,0,0,38,209,1,0,0,0,40,212,1,0,0,0,42,215,1,0,0,0,44,218,1,0,
0,0,46,221,1,0,0,0,48,224,1,0,0,0,50,227,1,0,0,0,52,230,1,0,0,0,54,233,1,
0,0,0,56,236,1,0,0,0,58,239,1,0,0,0,60,242,1,0,0,0,62,245,1,0,0,0,64,248,
1,0,0,0,66,251,1,0,0,0,68,254,1,0,0,0,70,257,1,0,0,0,72,260,1,0,0,0,74,263,
1,0,0,0,76,266,1,0,0,0,78,270,1,0,0,0,80,274,1,0,0,0,82,283,1,0,0,0,84,285,
1,0,0,0,86,314,1,0,0,0,88,316,1,0,0,0,90,324,1,0,0,0,92,326,1,0,0,0,94,336,
1,0,0,0,96,338,1,0,0,0,98,346,1,0,0,0,100,356,1,0,0,0,102,361,1,0,0,0,104,
366,1,0,0,0,106,383,1,0,0,0,108,391,1,0,0,0,110,393,1,0,0,0,112,403,1,0,
0,0,114,444,1,0,0,0,116,452,1,0,0,0,118,454,1,0,0,0,120,464,1,0,0,0,122,
466,1,0,0,0,124,476,1,0,0,0,126,502,1,0,0,0,128,541,1,0,0,0,130,557,1,0,
0,0,132,571,1,0,0,0,134,653,1,0,0,0,136,664,1,0,0,0,138,689,1,0,0,0,140,
710,1,0,0,0,142,720,1,0,0,0,144,728,1,0,0,0,146,730,1,0,0,0,148,740,1,0,
0,0,150,742,1,0,0,0,152,153,3,76,38,0,153,154,5,0,0,1,154,1,1,0,0,0,155,
156,3,78,39,0,156,157,5,0,0,1,157,3,1,0,0,0,158,159,3,80,40,0,159,160,5,
0,0,1,160,5,1,0,0,0,161,162,3,82,41,0,162,163,5,0,0,1,163,7,1,0,0,0,164,
165,3,84,42,0,165,166,5,0,0,1,166,9,1,0,0,0,167,168,3,86,43,0,168,169,5,
0,0,1,169,11,1,0,0,0,170,171,3,88,44,0,171,172,5,0,0,1,172,13,1,0,0,0,173,
174,3,90,45,0,174,175,5,0,0,1,175,15,1,0,0,0,176,177,3,92,46,0,177,178,5,
0,0,1,178,17,1,0,0,0,179,180,3,94,47,0,180,181,5,0,0,1,181,19,1,0,0,0,182,
183,3,96,48,0,183,184,5,0,0,1,184,21,1,0,0,0,185,186,3,98,49,0,186,187,5,
0,0,1,187,23,1,0,0,0,188,189,3,100,50,0,189,190,5,0,0,1,190,25,1,0,0,0,191,
192,3,102,51,0,192,193,5,0,0,1,193,27,1,0,0,0,194,195,3,104,52,0,195,196,
5,0,0,1,196,29,1,0,0,0,197,198,3,106,53,0,198,199,5,0,0,1,199,31,1,0,0,0,
200,201,3,108,54,0,201,202,5,0,0,1,202,33,1,0,0,0,203,204,3,110,55,0,204,
205,5,0,0,1,205,35,1,0,0,0,206,207,3,112,56,0,207,208,5,0,0,1,208,37,1,0,
0,0,209,210,3,114,57,0,210,211,5,0,0,1,211,39,1,0,0,0,212,213,3,116,58,0,
213,214,5,0,0,1,214,41,1,0,0,0,215,216,3,118,59,0,216,217,5,0,0,1,217,43,
1,0,0,0,218,219,3,120,60,0,219,220,5,0,0,1,220,45,1,0,0,0,221,222,3,122,
61,0,222,223,5,0,0,1,223,47,1,0,0,0,224,225,3,124,62,0,225,226,5,0,0,1,226,
49,1,0,0,0,227,228,3,126,63,0,228,229,5,0,0,1,229,51,1,0,0,0,230,231,3,128,
64,0,231,232,5,0,0,1,232,53,1,0,0,0,233,234,3,130,65,0,234,235,5,0,0,1,235,
55,1,0,0,0,236,237,3,132,66,0,237,238,5,0,0,1,238,57,1,0,0,0,239,240,3,134,
67,0,240,241,5,0,0,1,241,59,1,0,0,0,242,243,3,136,68,0,243,244,5,0,0,1,244,
61,1,0,0,0,245,246,3,138,69,0,246,247,5,0,0,1,247,63,1,0,0,0,248,249,3,140,
70,0,249,250,5,0,0,1,250,65,1,0,0,0,251,252,3,142,71,0,252,253,5,0,0,1,253,
67,1,0,0,0,254,255,3,144,72,0,255,256,5,0,0,1,256,69,1,0,0,0,257,258,3,146,
73,0,258,259,5,0,0,1,259,71,1,0,0,0,260,261,3,148,74,0,261,262,5,0,0,1,262,
73,1,0,0,0,263,264,3,150,75,0,264,265,5,0,0,1,265,75,1,0,0,0,266,267,3,78,
39,0,267,268,3,84,42,0,268,269,3,88,44,0,269,77,1,0,0,0,270,271,5,44,0,0,
271,272,5,34,0,0,272,273,5,1,0,0,273,79,1,0,0,0,274,275,5,36,0,0,275,276,
5,59,0,0,276,277,3,82,41,0,277,81,1,0,0,0,278,284,1,0,0,0,279,284,5,64,0,
0,280,281,5,64,0,0,281,282,5,2,0,0,282,284,3,82,41,0,283,278,1,0,0,0,283,
279,1,0,0,0,283,280,1,0,0,0,284,83,1,0,0,0,285,292,6,42,-1,0,286,287,10,
1,0,0,287,288,3,80,40,0,288,289,5,1,0,0,289,291,1,0,0,0,290,286,1,0,0,0,
291,294,1,0,0,0,292,290,1,0,0,0,292,293,1,0,0,0,293,85,1,0,0,0,294,292,1,
0,0,0,295,296,3,96,48,0,296,297,5,39,0,0,297,298,5,63,0,0,298,299,5,3,0,
0,299,300,3,100,50,0,300,301,5,4,0,0,301,302,3,102,51,0,302,303,3,104,52,
0,303,304,5,5,0,0,304,305,3,88,44,0,305,306,5,50,0,0,306,307,3,106,53,0,
307,308,5,1,0,0,308,309,5,6,0,0,309,315,1,0,0,0,310,311,5,56,0,0,311,312,
5,63,0,0,312,313,5,7,0,0,313,315,3,138,69,0,314,295,1,0,0,0,314,310,1,0,
0,0,315,87,1,0,0,0,316,321,6,44,-1,0,317,318,10,1,0,0,318,320,3,86,43,0,
319,317,1,0,0,0,320,323,1,0,0,0,321,319,1,0,0,0,321,322,1,0,0,0,322,89,1,
0,0,0,323,321,1,0,0,0,324,325,3,86,43,0,325,91,1,0,0,0,326,333,6,46,-1,0,
327,328,10,1,0,0,328,329,3,90,45,0,329,330,5,1,0,0,330,332,1,0,0,0,331,327,
1,0,0,0,332,335,1,0,0,0,333,331,1,0,0,0,333,334,1,0,0,0,334,93,1,0,0,0,335,
333,1,0,0,0,336,337,5,43,0,0,337,95,1,0,0,0,338,343,6,48,-1,0,339,340,10,
1,0,0,340,342,3,94,47,0,341,339,1,0,0,0,342,345,1,0,0,0,343,341,1,0,0,0,
343,344,1,0,0,0,344,97,1,0,0,0,345,343,1,0,0,0,346,347,5,63,0,0,347,348,
5,8,0,0,348,349,3,138,69,0,349,99,1,0,0,0,350,357,1,0,0,0,351,357,3,98,49,
0,352,353,3,98,49,0,353,354,5,2,0,0,354,355,3,100,50,0,355,357,1,0,0,0,356,
350,1,0,0,0,356,351,1,0,0,0,356,352,1,0,0,0,357,101,1,0,0,0,358,362,1,0,
0,0,359,360,5,9,0,0,360,362,3,138,69,0,361,358,1,0,0,0,361,359,1,0,0,0,362,
103,1,0,0,0,363,367,1,0,0,0,364,365,5,54,0,0,365,367,3,144,72,0,366,363,
1,0,0,0,366,364,1,0,0,0,367,105,1,0,0,0,368,369,5,41,0,0,369,370,3,106,53,
0,370,371,5,53,0,0,371,372,3,106,53,0,372,373,5,35,0,0,373,374,3,106,53,
0,374,384,1,0,0,0,375,376,5,45,0,0,376,377,5,63,0,0,377,378,5,7,0,0,378,
379,3,106,53,0,379,380,5,42,0,0,380,381,3,106,53,0,381,384,1,0,0,0,382,384,
3,128,64,0,383,368,1,0,0,0,383,375,1,0,0,0,383,382,1,0,0,0,384,107,1,0,0,
0,385,392,1,0,0,0,386,392,3,106,53,0,387,388,3,106,53,0,388,389,5,2,0,0,
389,390,3,108,54,0,390,392,1,0,0,0,391,385,1,0,0,0,391,386,1,0,0,0,391,387,
1,0,0,0,392,109,1,0,0,0,393,394,3,114,57,0,394,395,5,10,0,0,395,396,3,106,
53,0,396,111,1,0,0,0,397,404,1,0,0,0,398,404,3,110,55,0,399,400,3,110,55,
0,400,401,5,1,0,0,401,402,3,112,56,0,402,404,1,0,0,0,403,397,1,0,0,0,403,
398,1,0,0,0,403,399,1,0,0,0,404,113,1,0,0,0,405,406,5,11,0,0,406,407,5,63,
0,0,407,408,5,7,0,0,408,409,3,114,57,0,409,410,5,12,0,0,410,445,1,0,0,0,
411,412,5,5,0,0,412,413,3,116,58,0,413,414,5,6,0,0,414,445,1,0,0,0,415,416,
5,49,0,0,416,417,5,5,0,0,417,418,3,120,60,0,418,419,5,6,0,0,419,445,1,0,
0,0,420,421,5,13,0,0,421,422,3,116,58,0,422,423,5,14,0,0,423,445,1,0,0,0,
424,425,5,33,0,0,425,426,5,3,0,0,426,427,3,114,57,0,427,428,5,2,0,0,428,
429,3,114,57,0,429,430,5,4,0,0,430,445,1,0,0,0,431,445,5,37,0,0,432,445,
5,55,0,0,433,445,5,65,0,0,434,435,5,52,0,0,435,436,5,3,0,0,436,437,3,114,
57,0,437,438,5,4,0,0,438,445,1,0,0,0,439,445,5,63,0,0,440,441,5,3,0,0,441,
442,3,114,57,0,442,443,5,4,0,0,443,445,1,0,0,0,444,405,1,0,0,0,444,411,1,
0,0,0,444,415,1,0,0,0,444,420,1,0,0,0,444,424,1,0,0,0,444,431,1,0,0,0,444,
432,1,0,0,0,444,433,1,0,0,0,444,434,1,0,0,0,444,439,1,0,0,0,444,440,1,0,
0,0,445,115,1,0,0,0,446,453,1,0,0,0,447,453,3,114,57,0,448,449,3,114,57,
0,449,450,5,2,0,0,450,451,3,116,58,0,451,453,1,0,0,0,452,446,1,0,0,0,452,
447,1,0,0,0,452,448,1,0,0,0,453,117,1,0,0,0,454,455,5,63,0,0,455,456,5,7,
0,0,456,457,3,114,57,0,457,119,1,0,0,0,458,465,1,0,0,0,459,465,3,118,59,
0,460,461,3,118,59,0,461,462,5,2,0,0,462,463,3,120,60,0,463,465,1,0,0,0,
464,458,1,0,0,0,464,459,1,0,0,0,464,460,1,0,0,0,465,121,1,0,0,0,466,467,
5,63,0,0,467,468,5,7,0,0,468,469,3,106,53,0,469,123,1,0,0,0,470,477,1,0,
0,0,471,477,3,122,61,0,472,473,3,122,61,0,473,474,5,2,0,0,474,475,3,124,
62,0,475,477,1,0,0,0,476,470,1,0,0,0,476,471,1,0,0,0,476,472,1,0,0,0,477,
125,1,0,0,0,478,479,3,128,64,0,479,480,5,11,0,0,480,481,3,128,64,0,481,503,
1,0,0,0,482,483,3,128,64,0,483,484,5,15,0,0,484,485,3,128,64,0,485,503,1,
0,0,0,486,487,3,128,64,0,487,488,5,12,0,0,488,489,3,128,64,0,489,503,1,0,
0,0,490,491,3,128,64,0,491,492,5,16,0,0,492,493,3,128,64,0,493,503,1,0,0,
0,494,495,3,128,64,0,495,496,5,17,0,0,496,497,3,128,64,0,497,503,1,0,0,0,
498,499,3,128,64,0,499,500,5,18,0,0,500,501,3,128,64,0,501,503,1,0,0,0,502,
478,1,0,0,0,502,482,1,0,0,0,502,486,1,0,0,0,502,490,1,0,0,0,502,494,1,0,
0,0,502,498,1,0,0,0,503,127,1,0,0,0,504,505,6,64,-1,0,505,506,5,39,0,0,506,
507,5,3,0,0,507,508,3,100,50,0,508,509,5,4,0,0,509,510,5,5,0,0,510,511,5,
50,0,0,511,512,3,106,53,0,512,513,5,1,0,0,513,514,5,6,0,0,514,542,1,0,0,
0,515,516,5,5,0,0,516,517,3,108,54,0,517,518,5,6,0,0,518,542,1,0,0,0,519,
520,5,49,0,0,520,521,5,5,0,0,521,522,3,124,62,0,522,523,5,6,0,0,523,542,
1,0,0,0,524,525,5,11,0,0,525,526,5,63,0,0,526,527,5,7,0,0,527,528,3,106,
53,0,528,529,5,12,0,0,529,542,1,0,0,0,530,531,5,46,0,0,531,532,3,128,64,
0,532,533,5,5,0,0,533,534,3,112,56,0,534,535,5,6,0,0,535,542,1,0,0,0,536,
537,5,13,0,0,537,538,3,108,54,0,538,539,5,14,0,0,539,542,1,0,0,0,540,542,
3,130,65,0,541,504,1,0,0,0,541,515,1,0,0,0,541,519,1,0,0,0,541,524,1,0,0,
0,541,530,1,0,0,0,541,536,1,0,0,0,541,540,1,0,0,0,542,554,1,0,0,0,543,544,
10,10,0,0,544,545,5,32,0,0,545,553,3,138,69,0,546,547,10,3,0,0,547,548,5,
19,0,0,548,553,3,130,65,0,549,550,10,2,0,0,550,551,5,48,0,0,551,553,3,130,
65,0,552,543,1,0,0,0,552,546,1,0,0,0,552,549,1,0,0,0,553,556,1,0,0,0,554,
552,1,0,0,0,554,555,1,0,0,0,555,129,1,0,0,0,556,554,1,0,0,0,557,558,6,65,
-1,0,558,559,3,132,66,0,559,568,1,0,0,0,560,561,10,3,0,0,561,562,5,20,0,
0,562,567,3,132,66,0,563,564,10,2,0,0,564,565,5,31,0,0,565,567,3,132,66,
0,566,560,1,0,0,0,566,563,1,0,0,0,567,570,1,0,0,0,568,566,1,0,0,0,568,569,
1,0,0,0,569,131,1,0,0,0,570,568,1,0,0,0,571,572,6,66,-1,0,572,573,3,134,
67,0,573,581,1,0,0,0,574,575,10,2,0,0,575,576,5,3,0,0,576,577,3,108,54,0,
577,578,5,4,0,0,578,580,1,0,0,0,579,574,1,0,0,0,580,583,1,0,0,0,581,579,
1,0,0,0,581,582,1,0,0,0,582,133,1,0,0,0,583,581,1,0,0,0,584,585,5,33,0,0,
585,586,5,3,0,0,586,587,3,106,53,0,587,588,5,2,0,0,588,589,3,106,53,0,589,
590,5,4,0,0,590,654,1,0,0,0,591,592,5,21,0,0,592,593,5,3,0,0,593,594,3,106,
53,0,594,595,5,4,0,0,595,654,1,0,0,0,596,597,5,22,0,0,597,598,5,3,0,0,598,
599,3,106,53,0,599,600,5,4,0,0,600,654,1,0,0,0,601,602,5,23,0,0,602,603,
5,3,0,0,603,604,3,106,53,0,604,605,5,4,0,0,605,654,1,0,0,0,606,607,5,52,
0,0,607,608,5,3,0,0,608,609,3,106,53,0,609,610,5,4,0,0,610,654,1,0,0,0,611,
612,5,47,0,0,612,613,5,3,0,0,613,614,3,106,53,0,614,615,5,4,0,0,615,654,
1,0,0,0,616,617,5,24,0,0,617,618,5,3,0,0,618,619,3,106,53,0,619,620,5,4,
0,0,620,654,1,0,0,0,621,622,5,25,0,0,622,623,5,3,0,0,623,624,3,106,53,0,
624,625,5,4,0,0,625,654,1,0,0,0,626,627,5,38,0,0,627,628,5,3,0,0,628,629,
3,106,53,0,629,630,5,4,0,0,630,654,1,0,0,0,631,632,5,26,0,0,632,633,5,3,
0,0,633,634,3,106,53,0,634,635,5,2,0,0,635,636,3,106,53,0,636,637,5,2,0,
0,637,638,3,106,53,0,638,639,5,4,0,0,639,654,1,0,0,0,640,641,5,40,0,0,641,
642,5,13,0,0,642,643,3,138,69,0,643,644,5,14,0,0,644,645,3,136,68,0,645,
654,1,0,0,0,646,647,5,57,0,0,647,648,5,13,0,0,648,649,3,138,69,0,649,650,
5,14,0,0,650,651,3,136,68,0,651,654,1,0,0,0,652,654,3,136,68,0,653,584,1,
0,0,0,653,591,1,0,0,0,653,596,1,0,0,0,653,601,1,0,0,0,653,606,1,0,0,0,653,
611,1,0,0,0,653,616,1,0,0,0,653,621,1,0,0,0,653,626,1,0,0,0,653,631,1,0,
0,0,653,640,1,0,0,0,653,646,1,0,0,0,653,652,1,0,0,0,654,135,1,0,0,0,655,
656,6,68,-1,0,656,665,5,55,0,0,657,665,5,37,0,0,658,665,5,65,0,0,659,665,
5,63,0,0,660,661,5,3,0,0,661,662,3,106,53,0,662,663,5,4,0,0,663,665,1,0,
0,0,664,655,1,0,0,0,664,657,1,0,0,0,664,658,1,0,0,0,664,659,1,0,0,0,664,
660,1,0,0,0,665,674,1,0,0,0,666,667,10,7,0,0,667,668,5,27,0,0,668,673,5,
63,0,0,669,670,10,6,0,0,670,671,5,27,0,0,671,673,5,65,0,0,672,666,1,0,0,
0,672,669,1,0,0,0,673,676,1,0,0,0,674,672,1,0,0,0,674,675,1,0,0,0,675,137,
1,0,0,0,676,674,1,0,0,0,677,678,5,39,0,0,678,679,5,3,0,0,679,680,3,144,72,
0,680,681,5,4,0,0,681,682,5,9,0,0,682,683,3,138,69,0,683,690,1,0,0,0,684,
685,5,60,0,0,685,686,5,63,0,0,686,687,5,27,0,0,687,690,3,138,69,0,688,690,
3,140,70,0,689,677,1,0,0,0,689,684,1,0,0,0,689,688,1,0,0,0,690,139,1,0,0,
0,691,692,5,5,0,0,692,693,3,144,72,0,693,694,5,6,0,0,694,711,1,0,0,0,695,
696,5,51,0,0,696,697,5,5,0,0,697,698,3,148,74,0,698,699,5,6,0,0,699,711,
1,0,0,0,700,701,5,58,0,0,701,702,5,11,0,0,702,703,3,148,74,0,703,704,5,12,
0,0,704,711,1,0,0,0,705,706,5,13,0,0,706,707,3,138,69,0,707,708,5,14,0,0,
708,711,1,0,0,0,709,711,3,142,71,0,710,691,1,0,0,0,710,695,1,0,0,0,710,700,
1,0,0,0,710,705,1,0,0,0,710,709,1,0,0,0,711,141,1,0,0,0,712,721,5,28,0,0,
713,721,5,29,0,0,714,721,5,30,0,0,715,721,5,63,0,0,716,717,5,3,0,0,717,718,
3,138,69,0,718,719,5,4,0,0,719,721,1,0,0,0,720,712,1,0,0,0,720,713,1,0,0,
0,720,714,1,0,0,0,720,715,1,0,0,0,720,716,1,0,0,0,721,143,1,0,0,0,722,729,
1,0,0,0,723,729,3,138,69,0,724,725,3,138,69,0,725,726,5,2,0,0,726,727,3,
144,72,0,727,729,1,0,0,0,728,722,1,0,0,0,728,723,1,0,0,0,728,724,1,0,0,0,
729,145,1,0,0,0,730,731,5,63,0,0,731,732,5,8,0,0,732,733,3,138,69,0,733,
147,1,0,0,0,734,741,1,0,0,0,735,741,3,146,73,0,736,737,3,146,73,0,737,738,
5,2,0,0,738,739,3,148,74,0,739,741,1,0,0,0,740,734,1,0,0,0,740,735,1,0,0,
0,740,736,1,0,0,0,741,149,1,0,0,0,742,743,3,106,53,0,743,744,5,8,0,0,744,
745,3,138,69,0,745,151,1,0,0,0,32,283,292,314,321,333,343,356,361,366,383,
391,403,444,452,464,476,502,541,552,554,566,568,581,653,664,672,674,689,
710,720,728,740];


const atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

const decisionsToDFA = atn.decisionToState.map( (ds, index) => new antlr4.dfa.DFA(ds, index) );

const sharedContextCache = new antlr4.atn.PredictionContextCache();

export default class stellaParser extends antlr4.Parser {

    static grammarFileName = "stellaParser.g4";
    static literalNames = [ null, "';'", "','", "'('", "')'", "'{'", "'}'", 
                            "'='", "':'", "'->'", "'=>'", "'<'", "'>'", 
                            "'['", "']'", "'<='", "'>='", "'=='", "'!='", 
                            "'+'", "'*'", "'List::head'", "'List::isempty'", 
                            "'List::tail'", "'Nat::pred'", "'Nat::iszero'", 
                            "'Nat::rec'", "'.'", "'Bool'", "'Nat'", "'Unit'", 
                            "'and'", "'as'", "'cons'", "'core'", "'else'", 
                            "'extend'", "'false'", "'fix'", "'fn'", "'fold'", 
                            "'if'", "'in'", "'inline'", "'language'", "'let'", 
                            "'match'", "'not'", "'or'", "'record'", "'return'", 
                            "'struct'", "'succ'", "'then'", "'throws'", 
                            "'true'", "'type'", "'unfold'", "'variant'", 
                            "'with'", "'\\u00B5'" ];
    static symbolicNames = [ null, "Surrogate_id_SYMB_0", "Surrogate_id_SYMB_1", 
                             "Surrogate_id_SYMB_2", "Surrogate_id_SYMB_3", 
                             "Surrogate_id_SYMB_4", "Surrogate_id_SYMB_5", 
                             "Surrogate_id_SYMB_6", "Surrogate_id_SYMB_7", 
                             "Surrogate_id_SYMB_8", "Surrogate_id_SYMB_9", 
                             "Surrogate_id_SYMB_10", "Surrogate_id_SYMB_11", 
                             "Surrogate_id_SYMB_12", "Surrogate_id_SYMB_13", 
                             "Surrogate_id_SYMB_14", "Surrogate_id_SYMB_15", 
                             "Surrogate_id_SYMB_16", "Surrogate_id_SYMB_17", 
                             "Surrogate_id_SYMB_18", "Surrogate_id_SYMB_19", 
                             "Surrogate_id_SYMB_20", "Surrogate_id_SYMB_21", 
                             "Surrogate_id_SYMB_22", "Surrogate_id_SYMB_23", 
                             "Surrogate_id_SYMB_24", "Surrogate_id_SYMB_25", 
                             "Surrogate_id_SYMB_26", "Surrogate_id_SYMB_27", 
                             "Surrogate_id_SYMB_28", "Surrogate_id_SYMB_29", 
                             "Surrogate_id_SYMB_30", "Surrogate_id_SYMB_31", 
                             "Surrogate_id_SYMB_32", "Surrogate_id_SYMB_33", 
                             "Surrogate_id_SYMB_34", "Surrogate_id_SYMB_35", 
                             "Surrogate_id_SYMB_36", "Surrogate_id_SYMB_37", 
                             "Surrogate_id_SYMB_38", "Surrogate_id_SYMB_39", 
                             "Surrogate_id_SYMB_40", "Surrogate_id_SYMB_41", 
                             "Surrogate_id_SYMB_42", "Surrogate_id_SYMB_43", 
                             "Surrogate_id_SYMB_44", "Surrogate_id_SYMB_45", 
                             "Surrogate_id_SYMB_46", "Surrogate_id_SYMB_47", 
                             "Surrogate_id_SYMB_48", "Surrogate_id_SYMB_49", 
                             "Surrogate_id_SYMB_50", "Surrogate_id_SYMB_51", 
                             "Surrogate_id_SYMB_52", "Surrogate_id_SYMB_53", 
                             "Surrogate_id_SYMB_54", "Surrogate_id_SYMB_55", 
                             "Surrogate_id_SYMB_56", "Surrogate_id_SYMB_57", 
                             "Surrogate_id_SYMB_58", "Surrogate_id_SYMB_59", 
                             "COMMENT_antlr_builtin", "MULTICOMMENT_antlr_builtin", 
                             "StellaIdent", "ExtensionName", "INTEGER", 
                             "WS", "ErrorToken" ];
    static ruleNames = [ "start_Program", "start_LanguageDecl", "start_Extension", 
                         "start_ListExtensionName", "start_ListExtension", 
                         "start_Decl", "start_ListDecl", "start_LocalDecl", 
                         "start_ListLocalDecl", "start_Annotation", "start_ListAnnotation", 
                         "start_ParamDecl", "start_ListParamDecl", "start_ReturnType", 
                         "start_ThrowType", "start_Expr", "start_ListExpr", 
                         "start_MatchCase", "start_ListMatchCase", "start_Pattern", 
                         "start_ListPattern", "start_LabelledPattern", "start_ListLabelledPattern", 
                         "start_Binding", "start_ListBinding", "start_Expr0", 
                         "start_Expr1", "start_Expr2", "start_Expr3", "start_Expr4", 
                         "start_Expr5", "start_Type", "start_Type1", "start_Type2", 
                         "start_ListType", "start_FieldType", "start_ListFieldType", 
                         "start_Typing", "program", "languageDecl", "extension", 
                         "listExtensionName", "listExtension", "decl", "listDecl", 
                         "localDecl", "listLocalDecl", "annotation", "listAnnotation", 
                         "paramDecl", "listParamDecl", "returnType", "throwType", 
                         "expr", "listExpr", "matchCase", "listMatchCase", 
                         "pattern", "listPattern", "labelledPattern", "listLabelledPattern", 
                         "binding", "listBinding", "expr0", "expr1", "expr2", 
                         "expr3", "expr4", "expr5", "type", "type1", "type2", 
                         "listType", "fieldType", "listFieldType", "typing" ];

    constructor(input) {
        super(input);
        this._interp = new antlr4.atn.ParserATNSimulator(this, atn, decisionsToDFA, sharedContextCache);
        this.ruleNames = stellaParser.ruleNames;
        this.literalNames = stellaParser.literalNames;
        this.symbolicNames = stellaParser.symbolicNames;
    }

    sempred(localctx, ruleIndex, predIndex) {
    	switch(ruleIndex) {
    	case 42:
    	    		return this.listExtension_sempred(localctx, predIndex);
    	case 44:
    	    		return this.listDecl_sempred(localctx, predIndex);
    	case 46:
    	    		return this.listLocalDecl_sempred(localctx, predIndex);
    	case 48:
    	    		return this.listAnnotation_sempred(localctx, predIndex);
    	case 64:
    	    		return this.expr1_sempred(localctx, predIndex);
    	case 65:
    	    		return this.expr2_sempred(localctx, predIndex);
    	case 66:
    	    		return this.expr3_sempred(localctx, predIndex);
    	case 68:
    	    		return this.expr5_sempred(localctx, predIndex);
        default:
            throw "No predicate with index:" + ruleIndex;
       }
    }

    listExtension_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 0:
    			return this.precpred(this._ctx, 1);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    listDecl_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 1:
    			return this.precpred(this._ctx, 1);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    listLocalDecl_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 2:
    			return this.precpred(this._ctx, 1);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    listAnnotation_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 3:
    			return this.precpred(this._ctx, 1);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    expr1_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 4:
    			return this.precpred(this._ctx, 10);
    		case 5:
    			return this.precpred(this._ctx, 3);
    		case 6:
    			return this.precpred(this._ctx, 2);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    expr2_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 7:
    			return this.precpred(this._ctx, 3);
    		case 8:
    			return this.precpred(this._ctx, 2);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    expr3_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 9:
    			return this.precpred(this._ctx, 2);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };

    expr5_sempred(localctx, predIndex) {
    	switch(predIndex) {
    		case 10:
    			return this.precpred(this._ctx, 7);
    		case 11:
    			return this.precpred(this._ctx, 6);
    		default:
    			throw "No predicate with index:" + predIndex;
    	}
    };




	start_Program() {
	    let localctx = new Start_ProgramContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 0, stellaParser.RULE_start_Program);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 152;
	        localctx.x = this.program();
	        this.state = 153;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_LanguageDecl() {
	    let localctx = new Start_LanguageDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 2, stellaParser.RULE_start_LanguageDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 155;
	        localctx.x = this.languageDecl();
	        this.state = 156;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Extension() {
	    let localctx = new Start_ExtensionContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 4, stellaParser.RULE_start_Extension);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 158;
	        localctx.x = this.extension();
	        this.state = 159;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListExtensionName() {
	    let localctx = new Start_ListExtensionNameContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 6, stellaParser.RULE_start_ListExtensionName);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 161;
	        localctx.x = this.listExtensionName();
	        this.state = 162;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListExtension() {
	    let localctx = new Start_ListExtensionContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 8, stellaParser.RULE_start_ListExtension);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 164;
	        localctx.x = this.listExtension(0);
	        this.state = 165;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Decl() {
	    let localctx = new Start_DeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 10, stellaParser.RULE_start_Decl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 167;
	        localctx.x = this.decl();
	        this.state = 168;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListDecl() {
	    let localctx = new Start_ListDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 12, stellaParser.RULE_start_ListDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 170;
	        localctx.x = this.listDecl(0);
	        this.state = 171;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_LocalDecl() {
	    let localctx = new Start_LocalDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 14, stellaParser.RULE_start_LocalDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 173;
	        localctx.x = this.localDecl();
	        this.state = 174;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListLocalDecl() {
	    let localctx = new Start_ListLocalDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 16, stellaParser.RULE_start_ListLocalDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 176;
	        localctx.x = this.listLocalDecl(0);
	        this.state = 177;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Annotation() {
	    let localctx = new Start_AnnotationContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 18, stellaParser.RULE_start_Annotation);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 179;
	        localctx.x = this.annotation();
	        this.state = 180;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListAnnotation() {
	    let localctx = new Start_ListAnnotationContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 20, stellaParser.RULE_start_ListAnnotation);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 182;
	        localctx.x = this.listAnnotation(0);
	        this.state = 183;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ParamDecl() {
	    let localctx = new Start_ParamDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 22, stellaParser.RULE_start_ParamDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 185;
	        localctx.x = this.paramDecl();
	        this.state = 186;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListParamDecl() {
	    let localctx = new Start_ListParamDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 24, stellaParser.RULE_start_ListParamDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 188;
	        localctx.x = this.listParamDecl();
	        this.state = 189;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ReturnType() {
	    let localctx = new Start_ReturnTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 26, stellaParser.RULE_start_ReturnType);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 191;
	        localctx.x = this.returnType();
	        this.state = 192;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ThrowType() {
	    let localctx = new Start_ThrowTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 28, stellaParser.RULE_start_ThrowType);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 194;
	        localctx.x = this.throwType();
	        this.state = 195;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr() {
	    let localctx = new Start_ExprContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 30, stellaParser.RULE_start_Expr);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 197;
	        localctx.x = this.expr();
	        this.state = 198;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListExpr() {
	    let localctx = new Start_ListExprContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 32, stellaParser.RULE_start_ListExpr);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 200;
	        localctx.x = this.listExpr();
	        this.state = 201;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_MatchCase() {
	    let localctx = new Start_MatchCaseContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 34, stellaParser.RULE_start_MatchCase);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 203;
	        localctx.x = this.matchCase();
	        this.state = 204;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListMatchCase() {
	    let localctx = new Start_ListMatchCaseContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 36, stellaParser.RULE_start_ListMatchCase);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 206;
	        localctx.x = this.listMatchCase();
	        this.state = 207;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Pattern() {
	    let localctx = new Start_PatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 38, stellaParser.RULE_start_Pattern);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 209;
	        localctx.x = this.pattern();
	        this.state = 210;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListPattern() {
	    let localctx = new Start_ListPatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 40, stellaParser.RULE_start_ListPattern);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 212;
	        localctx.x = this.listPattern();
	        this.state = 213;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_LabelledPattern() {
	    let localctx = new Start_LabelledPatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 42, stellaParser.RULE_start_LabelledPattern);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 215;
	        localctx.x = this.labelledPattern();
	        this.state = 216;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListLabelledPattern() {
	    let localctx = new Start_ListLabelledPatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 44, stellaParser.RULE_start_ListLabelledPattern);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 218;
	        localctx.x = this.listLabelledPattern();
	        this.state = 219;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Binding() {
	    let localctx = new Start_BindingContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 46, stellaParser.RULE_start_Binding);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 221;
	        localctx.x = this.binding();
	        this.state = 222;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListBinding() {
	    let localctx = new Start_ListBindingContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 48, stellaParser.RULE_start_ListBinding);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 224;
	        localctx.x = this.listBinding();
	        this.state = 225;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr0() {
	    let localctx = new Start_Expr0Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 50, stellaParser.RULE_start_Expr0);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 227;
	        localctx.x = this.expr0();
	        this.state = 228;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr1() {
	    let localctx = new Start_Expr1Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 52, stellaParser.RULE_start_Expr1);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 230;
	        localctx.x = this.expr1(0);
	        this.state = 231;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr2() {
	    let localctx = new Start_Expr2Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 54, stellaParser.RULE_start_Expr2);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 233;
	        localctx.x = this.expr2(0);
	        this.state = 234;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr3() {
	    let localctx = new Start_Expr3Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 56, stellaParser.RULE_start_Expr3);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 236;
	        localctx.x = this.expr3(0);
	        this.state = 237;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr4() {
	    let localctx = new Start_Expr4Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 58, stellaParser.RULE_start_Expr4);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 239;
	        localctx.x = this.expr4();
	        this.state = 240;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Expr5() {
	    let localctx = new Start_Expr5Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 60, stellaParser.RULE_start_Expr5);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 242;
	        localctx.x = this.expr5(0);
	        this.state = 243;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Type() {
	    let localctx = new Start_TypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 62, stellaParser.RULE_start_Type);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 245;
	        localctx.x = this.type();
	        this.state = 246;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Type1() {
	    let localctx = new Start_Type1Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 64, stellaParser.RULE_start_Type1);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 248;
	        localctx.x = this.type1();
	        this.state = 249;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Type2() {
	    let localctx = new Start_Type2Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 66, stellaParser.RULE_start_Type2);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 251;
	        localctx.x = this.type2();
	        this.state = 252;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListType() {
	    let localctx = new Start_ListTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 68, stellaParser.RULE_start_ListType);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 254;
	        localctx.x = this.listType();
	        this.state = 255;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_FieldType() {
	    let localctx = new Start_FieldTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 70, stellaParser.RULE_start_FieldType);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 257;
	        localctx.x = this.fieldType();
	        this.state = 258;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_ListFieldType() {
	    let localctx = new Start_ListFieldTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 72, stellaParser.RULE_start_ListFieldType);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 260;
	        localctx.x = this.listFieldType();
	        this.state = 261;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	start_Typing() {
	    let localctx = new Start_TypingContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 74, stellaParser.RULE_start_Typing);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 263;
	        localctx.x = this.typing();
	        this.state = 264;
	        this.match(stellaParser.EOF);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	program() {
	    let localctx = new ProgramContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 76, stellaParser.RULE_program);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 266;
	        localctx.p_1_1 = this.languageDecl();
	        this.state = 267;
	        localctx.p_1_2 = this.listExtension(0);
	        this.state = 268;
	        localctx.p_1_3 = this.listDecl(0);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	languageDecl() {
	    let localctx = new LanguageDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 78, stellaParser.RULE_languageDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 270;
	        this.match(stellaParser.Surrogate_id_SYMB_43);
	        this.state = 271;
	        this.match(stellaParser.Surrogate_id_SYMB_33);
	        this.state = 272;
	        this.match(stellaParser.Surrogate_id_SYMB_0);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	extension() {
	    let localctx = new ExtensionContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 80, stellaParser.RULE_extension);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 274;
	        this.match(stellaParser.Surrogate_id_SYMB_35);
	        this.state = 275;
	        this.match(stellaParser.Surrogate_id_SYMB_58);
	        this.state = 276;
	        localctx.p_1_3 = this.listExtensionName();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listExtensionName() {
	    let localctx = new ListExtensionNameContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 82, stellaParser.RULE_listExtensionName);
	    try {
	        this.state = 283;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,0,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 279;
	            localctx.p_2_1 = this.match(stellaParser.ExtensionName);
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 280;
	            localctx.p_3_1 = this.match(stellaParser.ExtensionName);
	            this.state = 281;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 282;
	            localctx.p_3_3 = this.listExtensionName();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


	listExtension(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new ListExtensionContext(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 84;
	    this.enterRecursionRule(localctx, 84, stellaParser.RULE_listExtension, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 292;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,1,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                localctx = new ListExtensionContext(this, _parentctx, _parentState);
	                localctx.p_2_1 = _prevctx;
	                this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_listExtension);
	                this.state = 286;
	                if (!( this.precpred(this._ctx, 1))) {
	                    throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 1)");
	                }
	                this.state = 287;
	                localctx.p_2_2 = this.extension();
	                this.state = 288;
	                this.match(stellaParser.Surrogate_id_SYMB_0); 
	            }
	            this.state = 294;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,1,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}



	decl() {
	    let localctx = new DeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 86, stellaParser.RULE_decl);
	    try {
	        this.state = 314;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,2,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 295;
	            localctx.p_1_1 = this.listAnnotation(0);
	            this.state = 296;
	            this.match(stellaParser.Surrogate_id_SYMB_38);
	            this.state = 297;
	            localctx.p_1_3 = this.match(stellaParser.StellaIdent);
	            this.state = 298;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 299;
	            localctx.p_1_5 = this.listParamDecl();
	            this.state = 300;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            this.state = 301;
	            localctx.p_1_7 = this.returnType();
	            this.state = 302;
	            localctx.p_1_8 = this.throwType();
	            this.state = 303;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 304;
	            localctx.p_1_10 = this.listDecl(0);
	            this.state = 305;
	            this.match(stellaParser.Surrogate_id_SYMB_49);
	            this.state = 306;
	            localctx.p_1_12 = this.expr();
	            this.state = 307;
	            this.match(stellaParser.Surrogate_id_SYMB_0);
	            this.state = 308;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 310;
	            this.match(stellaParser.Surrogate_id_SYMB_55);
	            this.state = 311;
	            localctx.p_2_2 = this.match(stellaParser.StellaIdent);
	            this.state = 312;
	            this.match(stellaParser.Surrogate_id_SYMB_6);
	            this.state = 313;
	            localctx.p_2_4 = this.type();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


	listDecl(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new ListDeclContext(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 88;
	    this.enterRecursionRule(localctx, 88, stellaParser.RULE_listDecl, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 321;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,3,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                localctx = new ListDeclContext(this, _parentctx, _parentState);
	                localctx.p_2_1 = _prevctx;
	                this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_listDecl);
	                this.state = 317;
	                if (!( this.precpred(this._ctx, 1))) {
	                    throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 1)");
	                }
	                this.state = 318;
	                localctx.p_2_2 = this.decl(); 
	            }
	            this.state = 323;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,3,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}



	localDecl() {
	    let localctx = new LocalDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 90, stellaParser.RULE_localDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 324;
	        localctx.p_1_1 = this.decl();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


	listLocalDecl(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new ListLocalDeclContext(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 92;
	    this.enterRecursionRule(localctx, 92, stellaParser.RULE_listLocalDecl, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 333;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,4,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                localctx = new ListLocalDeclContext(this, _parentctx, _parentState);
	                localctx.p_2_1 = _prevctx;
	                this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_listLocalDecl);
	                this.state = 327;
	                if (!( this.precpred(this._ctx, 1))) {
	                    throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 1)");
	                }
	                this.state = 328;
	                localctx.p_2_2 = this.localDecl();
	                this.state = 329;
	                this.match(stellaParser.Surrogate_id_SYMB_0); 
	            }
	            this.state = 335;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,4,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}



	annotation() {
	    let localctx = new AnnotationContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 94, stellaParser.RULE_annotation);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 336;
	        this.match(stellaParser.Surrogate_id_SYMB_42);
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


	listAnnotation(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new ListAnnotationContext(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 96;
	    this.enterRecursionRule(localctx, 96, stellaParser.RULE_listAnnotation, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 343;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,5,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                localctx = new ListAnnotationContext(this, _parentctx, _parentState);
	                localctx.p_2_1 = _prevctx;
	                this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_listAnnotation);
	                this.state = 339;
	                if (!( this.precpred(this._ctx, 1))) {
	                    throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 1)");
	                }
	                this.state = 340;
	                localctx.p_2_2 = this.annotation(); 
	            }
	            this.state = 345;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,5,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}



	paramDecl() {
	    let localctx = new ParamDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 98, stellaParser.RULE_paramDecl);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 346;
	        localctx.p_1_1 = this.match(stellaParser.StellaIdent);
	        this.state = 347;
	        this.match(stellaParser.Surrogate_id_SYMB_7);
	        this.state = 348;
	        localctx.p_1_3 = this.type();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listParamDecl() {
	    let localctx = new ListParamDeclContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 100, stellaParser.RULE_listParamDecl);
	    try {
	        this.state = 356;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,6,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 351;
	            localctx.p_2_1 = this.paramDecl();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 352;
	            localctx.p_3_1 = this.paramDecl();
	            this.state = 353;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 354;
	            localctx.p_3_3 = this.listParamDecl();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	returnType() {
	    let localctx = new ReturnTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 102, stellaParser.RULE_returnType);
	    try {
	        this.state = 361;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case -1:
	        case 5:
	        case 54:
	            this.enterOuterAlt(localctx, 1);

	            break;
	        case 9:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 359;
	            this.match(stellaParser.Surrogate_id_SYMB_8);
	            this.state = 360;
	            localctx.p_2_2 = this.type();
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	throwType() {
	    let localctx = new ThrowTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 104, stellaParser.RULE_throwType);
	    try {
	        this.state = 366;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case -1:
	        case 5:
	            this.enterOuterAlt(localctx, 1);

	            break;
	        case 54:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 364;
	            this.match(stellaParser.Surrogate_id_SYMB_53);
	            this.state = 365;
	            localctx.p_2_2 = this.listType();
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	expr() {
	    let localctx = new ExprContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 106, stellaParser.RULE_expr);
	    try {
	        this.state = 383;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 41:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 368;
	            this.match(stellaParser.Surrogate_id_SYMB_40);
	            this.state = 369;
	            localctx.p_1_2 = this.expr();
	            this.state = 370;
	            this.match(stellaParser.Surrogate_id_SYMB_52);
	            this.state = 371;
	            localctx.p_1_4 = this.expr();
	            this.state = 372;
	            this.match(stellaParser.Surrogate_id_SYMB_34);
	            this.state = 373;
	            localctx.p_1_6 = this.expr();
	            break;
	        case 45:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 375;
	            this.match(stellaParser.Surrogate_id_SYMB_44);
	            this.state = 376;
	            localctx.p_2_2 = this.match(stellaParser.StellaIdent);
	            this.state = 377;
	            this.match(stellaParser.Surrogate_id_SYMB_6);
	            this.state = 378;
	            localctx.p_2_4 = this.expr();
	            this.state = 379;
	            this.match(stellaParser.Surrogate_id_SYMB_41);
	            this.state = 380;
	            localctx.p_2_6 = this.expr();
	            break;
	        case 3:
	        case 5:
	        case 11:
	        case 13:
	        case 21:
	        case 22:
	        case 23:
	        case 24:
	        case 25:
	        case 26:
	        case 33:
	        case 37:
	        case 38:
	        case 39:
	        case 40:
	        case 46:
	        case 47:
	        case 49:
	        case 52:
	        case 55:
	        case 57:
	        case 63:
	        case 65:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 382;
	            localctx.p_3_1 = this.expr1(0);
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listExpr() {
	    let localctx = new ListExprContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 108, stellaParser.RULE_listExpr);
	    try {
	        this.state = 391;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,10,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 386;
	            localctx.p_2_1 = this.expr();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 387;
	            localctx.p_3_1 = this.expr();
	            this.state = 388;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 389;
	            localctx.p_3_3 = this.listExpr();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	matchCase() {
	    let localctx = new MatchCaseContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 110, stellaParser.RULE_matchCase);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 393;
	        localctx.p_1_1 = this.pattern();
	        this.state = 394;
	        this.match(stellaParser.Surrogate_id_SYMB_9);
	        this.state = 395;
	        localctx.p_1_3 = this.expr();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listMatchCase() {
	    let localctx = new ListMatchCaseContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 112, stellaParser.RULE_listMatchCase);
	    try {
	        this.state = 403;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,11,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 398;
	            localctx.p_2_1 = this.matchCase();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 399;
	            localctx.p_3_1 = this.matchCase();
	            this.state = 400;
	            this.match(stellaParser.Surrogate_id_SYMB_0);
	            this.state = 401;
	            localctx.p_3_3 = this.listMatchCase();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	pattern() {
	    let localctx = new PatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 114, stellaParser.RULE_pattern);
	    try {
	        this.state = 444;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 11:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 405;
	            this.match(stellaParser.Surrogate_id_SYMB_10);
	            this.state = 406;
	            localctx.p_1_2 = this.match(stellaParser.StellaIdent);
	            this.state = 407;
	            this.match(stellaParser.Surrogate_id_SYMB_6);
	            this.state = 408;
	            localctx.p_1_4 = this.pattern();
	            this.state = 409;
	            this.match(stellaParser.Surrogate_id_SYMB_11);
	            break;
	        case 5:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 411;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 412;
	            localctx.p_2_2 = this.listPattern();
	            this.state = 413;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 49:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 415;
	            this.match(stellaParser.Surrogate_id_SYMB_48);
	            this.state = 416;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 417;
	            localctx.p_3_3 = this.listLabelledPattern();
	            this.state = 418;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 13:
	            this.enterOuterAlt(localctx, 4);
	            this.state = 420;
	            this.match(stellaParser.Surrogate_id_SYMB_12);
	            this.state = 421;
	            localctx.p_4_2 = this.listPattern();
	            this.state = 422;
	            this.match(stellaParser.Surrogate_id_SYMB_13);
	            break;
	        case 33:
	            this.enterOuterAlt(localctx, 5);
	            this.state = 424;
	            this.match(stellaParser.Surrogate_id_SYMB_32);
	            this.state = 425;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 426;
	            localctx.p_5_3 = this.pattern();
	            this.state = 427;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 428;
	            localctx.p_5_5 = this.pattern();
	            this.state = 429;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 37:
	            this.enterOuterAlt(localctx, 6);
	            this.state = 431;
	            this.match(stellaParser.Surrogate_id_SYMB_36);
	            break;
	        case 55:
	            this.enterOuterAlt(localctx, 7);
	            this.state = 432;
	            this.match(stellaParser.Surrogate_id_SYMB_54);
	            break;
	        case 65:
	            this.enterOuterAlt(localctx, 8);
	            this.state = 433;
	            localctx.p_8_1 = this.match(stellaParser.INTEGER);
	            break;
	        case 52:
	            this.enterOuterAlt(localctx, 9);
	            this.state = 434;
	            this.match(stellaParser.Surrogate_id_SYMB_51);
	            this.state = 435;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 436;
	            localctx.p_9_3 = this.pattern();
	            this.state = 437;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 63:
	            this.enterOuterAlt(localctx, 10);
	            this.state = 439;
	            localctx.p_10_1 = this.match(stellaParser.StellaIdent);
	            break;
	        case 3:
	            this.enterOuterAlt(localctx, 11);
	            this.state = 440;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 441;
	            localctx.p_11_2 = this.pattern();
	            this.state = 442;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listPattern() {
	    let localctx = new ListPatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 116, stellaParser.RULE_listPattern);
	    try {
	        this.state = 452;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,13,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 447;
	            localctx.p_2_1 = this.pattern();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 448;
	            localctx.p_3_1 = this.pattern();
	            this.state = 449;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 450;
	            localctx.p_3_3 = this.listPattern();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	labelledPattern() {
	    let localctx = new LabelledPatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 118, stellaParser.RULE_labelledPattern);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 454;
	        localctx.p_1_1 = this.match(stellaParser.StellaIdent);
	        this.state = 455;
	        this.match(stellaParser.Surrogate_id_SYMB_6);
	        this.state = 456;
	        localctx.p_1_3 = this.pattern();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listLabelledPattern() {
	    let localctx = new ListLabelledPatternContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 120, stellaParser.RULE_listLabelledPattern);
	    try {
	        this.state = 464;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,14,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 459;
	            localctx.p_2_1 = this.labelledPattern();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 460;
	            localctx.p_3_1 = this.labelledPattern();
	            this.state = 461;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 462;
	            localctx.p_3_3 = this.listLabelledPattern();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	binding() {
	    let localctx = new BindingContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 122, stellaParser.RULE_binding);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 466;
	        localctx.p_1_1 = this.match(stellaParser.StellaIdent);
	        this.state = 467;
	        this.match(stellaParser.Surrogate_id_SYMB_6);
	        this.state = 468;
	        localctx.p_1_3 = this.expr();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listBinding() {
	    let localctx = new ListBindingContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 124, stellaParser.RULE_listBinding);
	    try {
	        this.state = 476;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,15,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 471;
	            localctx.p_2_1 = this.binding();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 472;
	            localctx.p_3_1 = this.binding();
	            this.state = 473;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 474;
	            localctx.p_3_3 = this.listBinding();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	expr0() {
	    let localctx = new Expr0Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 126, stellaParser.RULE_expr0);
	    try {
	        this.state = 502;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,16,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 478;
	            localctx.p_1_1 = this.expr1(0);
	            this.state = 479;
	            this.match(stellaParser.Surrogate_id_SYMB_10);
	            this.state = 480;
	            localctx.p_1_3 = this.expr1(0);
	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 482;
	            localctx.p_2_1 = this.expr1(0);
	            this.state = 483;
	            this.match(stellaParser.Surrogate_id_SYMB_14);
	            this.state = 484;
	            localctx.p_2_3 = this.expr1(0);
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 486;
	            localctx.p_3_1 = this.expr1(0);
	            this.state = 487;
	            this.match(stellaParser.Surrogate_id_SYMB_11);
	            this.state = 488;
	            localctx.p_3_3 = this.expr1(0);
	            break;

	        case 4:
	            this.enterOuterAlt(localctx, 4);
	            this.state = 490;
	            localctx.p_4_1 = this.expr1(0);
	            this.state = 491;
	            this.match(stellaParser.Surrogate_id_SYMB_15);
	            this.state = 492;
	            localctx.p_4_3 = this.expr1(0);
	            break;

	        case 5:
	            this.enterOuterAlt(localctx, 5);
	            this.state = 494;
	            localctx.p_5_1 = this.expr1(0);
	            this.state = 495;
	            this.match(stellaParser.Surrogate_id_SYMB_16);
	            this.state = 496;
	            localctx.p_5_3 = this.expr1(0);
	            break;

	        case 6:
	            this.enterOuterAlt(localctx, 6);
	            this.state = 498;
	            localctx.p_6_1 = this.expr1(0);
	            this.state = 499;
	            this.match(stellaParser.Surrogate_id_SYMB_17);
	            this.state = 500;
	            localctx.p_6_3 = this.expr1(0);
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


	expr1(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new Expr1Context(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 128;
	    this.enterRecursionRule(localctx, 128, stellaParser.RULE_expr1, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 541;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 39:
	            this.state = 505;
	            this.match(stellaParser.Surrogate_id_SYMB_38);
	            this.state = 506;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 507;
	            localctx.p_2_3 = this.listParamDecl();
	            this.state = 508;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            this.state = 509;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 510;
	            this.match(stellaParser.Surrogate_id_SYMB_49);
	            this.state = 511;
	            localctx.p_2_7 = this.expr();
	            this.state = 512;
	            this.match(stellaParser.Surrogate_id_SYMB_0);
	            this.state = 513;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 5:
	            this.state = 515;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 516;
	            localctx.p_3_2 = this.listExpr();
	            this.state = 517;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 49:
	            this.state = 519;
	            this.match(stellaParser.Surrogate_id_SYMB_48);
	            this.state = 520;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 521;
	            localctx.p_4_3 = this.listBinding();
	            this.state = 522;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 11:
	            this.state = 524;
	            this.match(stellaParser.Surrogate_id_SYMB_10);
	            this.state = 525;
	            localctx.p_5_2 = this.match(stellaParser.StellaIdent);
	            this.state = 526;
	            this.match(stellaParser.Surrogate_id_SYMB_6);
	            this.state = 527;
	            localctx.p_5_4 = this.expr();
	            this.state = 528;
	            this.match(stellaParser.Surrogate_id_SYMB_11);
	            break;
	        case 46:
	            this.state = 530;
	            this.match(stellaParser.Surrogate_id_SYMB_45);
	            this.state = 531;
	            localctx.p_6_2 = this.expr1(0);
	            this.state = 532;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 533;
	            localctx.p_6_4 = this.listMatchCase();
	            this.state = 534;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 13:
	            this.state = 536;
	            this.match(stellaParser.Surrogate_id_SYMB_12);
	            this.state = 537;
	            localctx.p_7_2 = this.listExpr();
	            this.state = 538;
	            this.match(stellaParser.Surrogate_id_SYMB_13);
	            break;
	        case 3:
	        case 21:
	        case 22:
	        case 23:
	        case 24:
	        case 25:
	        case 26:
	        case 33:
	        case 37:
	        case 38:
	        case 40:
	        case 47:
	        case 52:
	        case 55:
	        case 57:
	        case 63:
	        case 65:
	            this.state = 540;
	            localctx.p_10_1 = this.expr2(0);
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 554;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,19,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                this.state = 552;
	                this._errHandler.sync(this);
	                var la_ = this._interp.adaptivePredict(this._input,18,this._ctx);
	                switch(la_) {
	                case 1:
	                    localctx = new Expr1Context(this, _parentctx, _parentState);
	                    localctx.p_1_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr1);
	                    this.state = 543;
	                    if (!( this.precpred(this._ctx, 10))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 10)");
	                    }
	                    this.state = 544;
	                    this.match(stellaParser.Surrogate_id_SYMB_31);
	                    this.state = 545;
	                    localctx.p_1_3 = this.type();
	                    break;

	                case 2:
	                    localctx = new Expr1Context(this, _parentctx, _parentState);
	                    localctx.p_8_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr1);
	                    this.state = 546;
	                    if (!( this.precpred(this._ctx, 3))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 3)");
	                    }
	                    this.state = 547;
	                    this.match(stellaParser.Surrogate_id_SYMB_18);
	                    this.state = 548;
	                    localctx.p_8_3 = this.expr2(0);
	                    break;

	                case 3:
	                    localctx = new Expr1Context(this, _parentctx, _parentState);
	                    localctx.p_9_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr1);
	                    this.state = 549;
	                    if (!( this.precpred(this._ctx, 2))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 2)");
	                    }
	                    this.state = 550;
	                    this.match(stellaParser.Surrogate_id_SYMB_47);
	                    this.state = 551;
	                    localctx.p_9_3 = this.expr2(0);
	                    break;

	                } 
	            }
	            this.state = 556;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,19,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}


	expr2(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new Expr2Context(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 130;
	    this.enterRecursionRule(localctx, 130, stellaParser.RULE_expr2, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 558;
	        localctx.p_3_1 = this.expr3(0);
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 568;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,21,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                this.state = 566;
	                this._errHandler.sync(this);
	                var la_ = this._interp.adaptivePredict(this._input,20,this._ctx);
	                switch(la_) {
	                case 1:
	                    localctx = new Expr2Context(this, _parentctx, _parentState);
	                    localctx.p_1_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr2);
	                    this.state = 560;
	                    if (!( this.precpred(this._ctx, 3))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 3)");
	                    }
	                    this.state = 561;
	                    this.match(stellaParser.Surrogate_id_SYMB_19);
	                    this.state = 562;
	                    localctx.p_1_3 = this.expr3(0);
	                    break;

	                case 2:
	                    localctx = new Expr2Context(this, _parentctx, _parentState);
	                    localctx.p_2_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr2);
	                    this.state = 563;
	                    if (!( this.precpred(this._ctx, 2))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 2)");
	                    }
	                    this.state = 564;
	                    this.match(stellaParser.Surrogate_id_SYMB_30);
	                    this.state = 565;
	                    localctx.p_2_3 = this.expr3(0);
	                    break;

	                } 
	            }
	            this.state = 570;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,21,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}


	expr3(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new Expr3Context(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 132;
	    this.enterRecursionRule(localctx, 132, stellaParser.RULE_expr3, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 572;
	        localctx.p_2_1 = this.expr4();
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 581;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,22,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                localctx = new Expr3Context(this, _parentctx, _parentState);
	                localctx.p_1_1 = _prevctx;
	                this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr3);
	                this.state = 574;
	                if (!( this.precpred(this._ctx, 2))) {
	                    throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 2)");
	                }
	                this.state = 575;
	                this.match(stellaParser.Surrogate_id_SYMB_2);
	                this.state = 576;
	                localctx.p_1_3 = this.listExpr();
	                this.state = 577;
	                this.match(stellaParser.Surrogate_id_SYMB_3); 
	            }
	            this.state = 583;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,22,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}



	expr4() {
	    let localctx = new Expr4Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 134, stellaParser.RULE_expr4);
	    try {
	        this.state = 653;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 33:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 584;
	            this.match(stellaParser.Surrogate_id_SYMB_32);
	            this.state = 585;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 586;
	            localctx.p_1_3 = this.expr();
	            this.state = 587;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 588;
	            localctx.p_1_5 = this.expr();
	            this.state = 589;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 21:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 591;
	            this.match(stellaParser.Surrogate_id_SYMB_20);
	            this.state = 592;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 593;
	            localctx.p_2_3 = this.expr();
	            this.state = 594;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 22:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 596;
	            this.match(stellaParser.Surrogate_id_SYMB_21);
	            this.state = 597;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 598;
	            localctx.p_3_3 = this.expr();
	            this.state = 599;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 23:
	            this.enterOuterAlt(localctx, 4);
	            this.state = 601;
	            this.match(stellaParser.Surrogate_id_SYMB_22);
	            this.state = 602;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 603;
	            localctx.p_4_3 = this.expr();
	            this.state = 604;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 52:
	            this.enterOuterAlt(localctx, 5);
	            this.state = 606;
	            this.match(stellaParser.Surrogate_id_SYMB_51);
	            this.state = 607;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 608;
	            localctx.p_5_3 = this.expr();
	            this.state = 609;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 47:
	            this.enterOuterAlt(localctx, 6);
	            this.state = 611;
	            this.match(stellaParser.Surrogate_id_SYMB_46);
	            this.state = 612;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 613;
	            localctx.p_6_3 = this.expr();
	            this.state = 614;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 24:
	            this.enterOuterAlt(localctx, 7);
	            this.state = 616;
	            this.match(stellaParser.Surrogate_id_SYMB_23);
	            this.state = 617;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 618;
	            localctx.p_7_3 = this.expr();
	            this.state = 619;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 25:
	            this.enterOuterAlt(localctx, 8);
	            this.state = 621;
	            this.match(stellaParser.Surrogate_id_SYMB_24);
	            this.state = 622;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 623;
	            localctx.p_8_3 = this.expr();
	            this.state = 624;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 38:
	            this.enterOuterAlt(localctx, 9);
	            this.state = 626;
	            this.match(stellaParser.Surrogate_id_SYMB_37);
	            this.state = 627;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 628;
	            localctx.p_9_3 = this.expr();
	            this.state = 629;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 26:
	            this.enterOuterAlt(localctx, 10);
	            this.state = 631;
	            this.match(stellaParser.Surrogate_id_SYMB_25);
	            this.state = 632;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 633;
	            localctx.p_10_3 = this.expr();
	            this.state = 634;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 635;
	            localctx.p_10_5 = this.expr();
	            this.state = 636;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 637;
	            localctx.p_10_7 = this.expr();
	            this.state = 638;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        case 40:
	            this.enterOuterAlt(localctx, 11);
	            this.state = 640;
	            this.match(stellaParser.Surrogate_id_SYMB_39);
	            this.state = 641;
	            this.match(stellaParser.Surrogate_id_SYMB_12);
	            this.state = 642;
	            localctx.p_11_3 = this.type();
	            this.state = 643;
	            this.match(stellaParser.Surrogate_id_SYMB_13);
	            this.state = 644;
	            localctx.p_11_5 = this.expr5(0);
	            break;
	        case 57:
	            this.enterOuterAlt(localctx, 12);
	            this.state = 646;
	            this.match(stellaParser.Surrogate_id_SYMB_56);
	            this.state = 647;
	            this.match(stellaParser.Surrogate_id_SYMB_12);
	            this.state = 648;
	            localctx.p_12_3 = this.type();
	            this.state = 649;
	            this.match(stellaParser.Surrogate_id_SYMB_13);
	            this.state = 650;
	            localctx.p_12_5 = this.expr5(0);
	            break;
	        case 3:
	        case 37:
	        case 55:
	        case 63:
	        case 65:
	            this.enterOuterAlt(localctx, 13);
	            this.state = 652;
	            localctx.p_13_1 = this.expr5(0);
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


	expr5(_p) {
		if(_p===undefined) {
		    _p = 0;
		}
	    const _parentctx = this._ctx;
	    const _parentState = this.state;
	    let localctx = new Expr5Context(this, this._ctx, _parentState);
	    let _prevctx = localctx;
	    const _startState = 136;
	    this.enterRecursionRule(localctx, 136, stellaParser.RULE_expr5, _p);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 664;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 55:
	            this.state = 656;
	            this.match(stellaParser.Surrogate_id_SYMB_54);
	            break;
	        case 37:
	            this.state = 657;
	            this.match(stellaParser.Surrogate_id_SYMB_36);
	            break;
	        case 65:
	            this.state = 658;
	            localctx.p_5_1 = this.match(stellaParser.INTEGER);
	            break;
	        case 63:
	            this.state = 659;
	            localctx.p_6_1 = this.match(stellaParser.StellaIdent);
	            break;
	        case 3:
	            this.state = 660;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 661;
	            localctx.p_7_2 = this.expr();
	            this.state = 662;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	        this._ctx.stop = this._input.LT(-1);
	        this.state = 674;
	        this._errHandler.sync(this);
	        var _alt = this._interp.adaptivePredict(this._input,26,this._ctx)
	        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
	            if(_alt===1) {
	                if(this._parseListeners!==null) {
	                    this.triggerExitRuleEvent();
	                }
	                _prevctx = localctx;
	                this.state = 672;
	                this._errHandler.sync(this);
	                var la_ = this._interp.adaptivePredict(this._input,25,this._ctx);
	                switch(la_) {
	                case 1:
	                    localctx = new Expr5Context(this, _parentctx, _parentState);
	                    localctx.p_1_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr5);
	                    this.state = 666;
	                    if (!( this.precpred(this._ctx, 7))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 7)");
	                    }
	                    this.state = 667;
	                    this.match(stellaParser.Surrogate_id_SYMB_26);
	                    this.state = 668;
	                    localctx.p_1_3 = this.match(stellaParser.StellaIdent);
	                    break;

	                case 2:
	                    localctx = new Expr5Context(this, _parentctx, _parentState);
	                    localctx.p_2_1 = _prevctx;
	                    this.pushNewRecursionContext(localctx, _startState, stellaParser.RULE_expr5);
	                    this.state = 669;
	                    if (!( this.precpred(this._ctx, 6))) {
	                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 6)");
	                    }
	                    this.state = 670;
	                    this.match(stellaParser.Surrogate_id_SYMB_26);
	                    this.state = 671;
	                    localctx.p_2_3 = this.match(stellaParser.INTEGER);
	                    break;

	                } 
	            }
	            this.state = 676;
	            this._errHandler.sync(this);
	            _alt = this._interp.adaptivePredict(this._input,26,this._ctx);
	        }

	    } catch( error) {
	        if(error instanceof antlr4.error.RecognitionException) {
		        localctx.exception = error;
		        this._errHandler.reportError(this, error);
		        this._errHandler.recover(this, error);
		    } else {
		    	throw error;
		    }
	    } finally {
	        this.unrollRecursionContexts(_parentctx)
	    }
	    return localctx;
	}



	type() {
	    let localctx = new TypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 138, stellaParser.RULE_type);
	    try {
	        this.state = 689;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 39:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 677;
	            this.match(stellaParser.Surrogate_id_SYMB_38);
	            this.state = 678;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 679;
	            localctx.p_1_3 = this.listType();
	            this.state = 680;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            this.state = 681;
	            this.match(stellaParser.Surrogate_id_SYMB_8);
	            this.state = 682;
	            localctx.p_1_6 = this.type();
	            break;
	        case 60:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 684;
	            this.match(stellaParser.Surrogate_id_SYMB_59);
	            this.state = 685;
	            localctx.p_2_2 = this.match(stellaParser.StellaIdent);
	            this.state = 686;
	            this.match(stellaParser.Surrogate_id_SYMB_26);
	            this.state = 687;
	            localctx.p_2_4 = this.type();
	            break;
	        case 3:
	        case 5:
	        case 13:
	        case 28:
	        case 29:
	        case 30:
	        case 51:
	        case 58:
	        case 63:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 688;
	            localctx.p_3_1 = this.type1();
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	type1() {
	    let localctx = new Type1Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 140, stellaParser.RULE_type1);
	    try {
	        this.state = 710;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 5:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 691;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 692;
	            localctx.p_1_2 = this.listType();
	            this.state = 693;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 51:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 695;
	            this.match(stellaParser.Surrogate_id_SYMB_50);
	            this.state = 696;
	            this.match(stellaParser.Surrogate_id_SYMB_4);
	            this.state = 697;
	            localctx.p_2_3 = this.listFieldType();
	            this.state = 698;
	            this.match(stellaParser.Surrogate_id_SYMB_5);
	            break;
	        case 58:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 700;
	            this.match(stellaParser.Surrogate_id_SYMB_57);
	            this.state = 701;
	            this.match(stellaParser.Surrogate_id_SYMB_10);
	            this.state = 702;
	            localctx.p_3_3 = this.listFieldType();
	            this.state = 703;
	            this.match(stellaParser.Surrogate_id_SYMB_11);
	            break;
	        case 13:
	            this.enterOuterAlt(localctx, 4);
	            this.state = 705;
	            this.match(stellaParser.Surrogate_id_SYMB_12);
	            this.state = 706;
	            localctx.p_4_2 = this.type();
	            this.state = 707;
	            this.match(stellaParser.Surrogate_id_SYMB_13);
	            break;
	        case 3:
	        case 28:
	        case 29:
	        case 30:
	        case 63:
	            this.enterOuterAlt(localctx, 5);
	            this.state = 709;
	            localctx.p_5_1 = this.type2();
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	type2() {
	    let localctx = new Type2Context(this, this._ctx, this.state);
	    this.enterRule(localctx, 142, stellaParser.RULE_type2);
	    try {
	        this.state = 720;
	        this._errHandler.sync(this);
	        switch(this._input.LA(1)) {
	        case 28:
	            this.enterOuterAlt(localctx, 1);
	            this.state = 712;
	            this.match(stellaParser.Surrogate_id_SYMB_27);
	            break;
	        case 29:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 713;
	            this.match(stellaParser.Surrogate_id_SYMB_28);
	            break;
	        case 30:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 714;
	            this.match(stellaParser.Surrogate_id_SYMB_29);
	            break;
	        case 63:
	            this.enterOuterAlt(localctx, 4);
	            this.state = 715;
	            localctx.p_4_1 = this.match(stellaParser.StellaIdent);
	            break;
	        case 3:
	            this.enterOuterAlt(localctx, 5);
	            this.state = 716;
	            this.match(stellaParser.Surrogate_id_SYMB_2);
	            this.state = 717;
	            localctx.p_5_2 = this.type();
	            this.state = 718;
	            this.match(stellaParser.Surrogate_id_SYMB_3);
	            break;
	        default:
	            throw new antlr4.error.NoViableAltException(this);
	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listType() {
	    let localctx = new ListTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 144, stellaParser.RULE_listType);
	    try {
	        this.state = 728;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,30,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 723;
	            localctx.p_2_1 = this.type();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 724;
	            localctx.p_3_1 = this.type();
	            this.state = 725;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 726;
	            localctx.p_3_3 = this.listType();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	fieldType() {
	    let localctx = new FieldTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 146, stellaParser.RULE_fieldType);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 730;
	        localctx.p_1_1 = this.match(stellaParser.StellaIdent);
	        this.state = 731;
	        this.match(stellaParser.Surrogate_id_SYMB_7);
	        this.state = 732;
	        localctx.p_1_3 = this.type();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	listFieldType() {
	    let localctx = new ListFieldTypeContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 148, stellaParser.RULE_listFieldType);
	    try {
	        this.state = 740;
	        this._errHandler.sync(this);
	        var la_ = this._interp.adaptivePredict(this._input,31,this._ctx);
	        switch(la_) {
	        case 1:
	            this.enterOuterAlt(localctx, 1);

	            break;

	        case 2:
	            this.enterOuterAlt(localctx, 2);
	            this.state = 735;
	            localctx.p_2_1 = this.fieldType();
	            break;

	        case 3:
	            this.enterOuterAlt(localctx, 3);
	            this.state = 736;
	            localctx.p_3_1 = this.fieldType();
	            this.state = 737;
	            this.match(stellaParser.Surrogate_id_SYMB_1);
	            this.state = 738;
	            localctx.p_3_3 = this.listFieldType();
	            break;

	        }
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}



	typing() {
	    let localctx = new TypingContext(this, this._ctx, this.state);
	    this.enterRule(localctx, 150, stellaParser.RULE_typing);
	    try {
	        this.enterOuterAlt(localctx, 1);
	        this.state = 742;
	        localctx.p_1_1 = this.expr();
	        this.state = 743;
	        this.match(stellaParser.Surrogate_id_SYMB_7);
	        this.state = 744;
	        localctx.p_1_3 = this.type();
	    } catch (re) {
	    	if(re instanceof antlr4.error.RecognitionException) {
		        localctx.exception = re;
		        this._errHandler.reportError(this, re);
		        this._errHandler.recover(this, re);
		    } else {
		    	throw re;
		    }
	    } finally {
	        this.exitRule();
	    }
	    return localctx;
	}


}

stellaParser.EOF = antlr4.Token.EOF;
stellaParser.Surrogate_id_SYMB_0 = 1;
stellaParser.Surrogate_id_SYMB_1 = 2;
stellaParser.Surrogate_id_SYMB_2 = 3;
stellaParser.Surrogate_id_SYMB_3 = 4;
stellaParser.Surrogate_id_SYMB_4 = 5;
stellaParser.Surrogate_id_SYMB_5 = 6;
stellaParser.Surrogate_id_SYMB_6 = 7;
stellaParser.Surrogate_id_SYMB_7 = 8;
stellaParser.Surrogate_id_SYMB_8 = 9;
stellaParser.Surrogate_id_SYMB_9 = 10;
stellaParser.Surrogate_id_SYMB_10 = 11;
stellaParser.Surrogate_id_SYMB_11 = 12;
stellaParser.Surrogate_id_SYMB_12 = 13;
stellaParser.Surrogate_id_SYMB_13 = 14;
stellaParser.Surrogate_id_SYMB_14 = 15;
stellaParser.Surrogate_id_SYMB_15 = 16;
stellaParser.Surrogate_id_SYMB_16 = 17;
stellaParser.Surrogate_id_SYMB_17 = 18;
stellaParser.Surrogate_id_SYMB_18 = 19;
stellaParser.Surrogate_id_SYMB_19 = 20;
stellaParser.Surrogate_id_SYMB_20 = 21;
stellaParser.Surrogate_id_SYMB_21 = 22;
stellaParser.Surrogate_id_SYMB_22 = 23;
stellaParser.Surrogate_id_SYMB_23 = 24;
stellaParser.Surrogate_id_SYMB_24 = 25;
stellaParser.Surrogate_id_SYMB_25 = 26;
stellaParser.Surrogate_id_SYMB_26 = 27;
stellaParser.Surrogate_id_SYMB_27 = 28;
stellaParser.Surrogate_id_SYMB_28 = 29;
stellaParser.Surrogate_id_SYMB_29 = 30;
stellaParser.Surrogate_id_SYMB_30 = 31;
stellaParser.Surrogate_id_SYMB_31 = 32;
stellaParser.Surrogate_id_SYMB_32 = 33;
stellaParser.Surrogate_id_SYMB_33 = 34;
stellaParser.Surrogate_id_SYMB_34 = 35;
stellaParser.Surrogate_id_SYMB_35 = 36;
stellaParser.Surrogate_id_SYMB_36 = 37;
stellaParser.Surrogate_id_SYMB_37 = 38;
stellaParser.Surrogate_id_SYMB_38 = 39;
stellaParser.Surrogate_id_SYMB_39 = 40;
stellaParser.Surrogate_id_SYMB_40 = 41;
stellaParser.Surrogate_id_SYMB_41 = 42;
stellaParser.Surrogate_id_SYMB_42 = 43;
stellaParser.Surrogate_id_SYMB_43 = 44;
stellaParser.Surrogate_id_SYMB_44 = 45;
stellaParser.Surrogate_id_SYMB_45 = 46;
stellaParser.Surrogate_id_SYMB_46 = 47;
stellaParser.Surrogate_id_SYMB_47 = 48;
stellaParser.Surrogate_id_SYMB_48 = 49;
stellaParser.Surrogate_id_SYMB_49 = 50;
stellaParser.Surrogate_id_SYMB_50 = 51;
stellaParser.Surrogate_id_SYMB_51 = 52;
stellaParser.Surrogate_id_SYMB_52 = 53;
stellaParser.Surrogate_id_SYMB_53 = 54;
stellaParser.Surrogate_id_SYMB_54 = 55;
stellaParser.Surrogate_id_SYMB_55 = 56;
stellaParser.Surrogate_id_SYMB_56 = 57;
stellaParser.Surrogate_id_SYMB_57 = 58;
stellaParser.Surrogate_id_SYMB_58 = 59;
stellaParser.Surrogate_id_SYMB_59 = 60;
stellaParser.COMMENT_antlr_builtin = 61;
stellaParser.MULTICOMMENT_antlr_builtin = 62;
stellaParser.StellaIdent = 63;
stellaParser.ExtensionName = 64;
stellaParser.INTEGER = 65;
stellaParser.WS = 66;
stellaParser.ErrorToken = 67;

stellaParser.RULE_start_Program = 0;
stellaParser.RULE_start_LanguageDecl = 1;
stellaParser.RULE_start_Extension = 2;
stellaParser.RULE_start_ListExtensionName = 3;
stellaParser.RULE_start_ListExtension = 4;
stellaParser.RULE_start_Decl = 5;
stellaParser.RULE_start_ListDecl = 6;
stellaParser.RULE_start_LocalDecl = 7;
stellaParser.RULE_start_ListLocalDecl = 8;
stellaParser.RULE_start_Annotation = 9;
stellaParser.RULE_start_ListAnnotation = 10;
stellaParser.RULE_start_ParamDecl = 11;
stellaParser.RULE_start_ListParamDecl = 12;
stellaParser.RULE_start_ReturnType = 13;
stellaParser.RULE_start_ThrowType = 14;
stellaParser.RULE_start_Expr = 15;
stellaParser.RULE_start_ListExpr = 16;
stellaParser.RULE_start_MatchCase = 17;
stellaParser.RULE_start_ListMatchCase = 18;
stellaParser.RULE_start_Pattern = 19;
stellaParser.RULE_start_ListPattern = 20;
stellaParser.RULE_start_LabelledPattern = 21;
stellaParser.RULE_start_ListLabelledPattern = 22;
stellaParser.RULE_start_Binding = 23;
stellaParser.RULE_start_ListBinding = 24;
stellaParser.RULE_start_Expr0 = 25;
stellaParser.RULE_start_Expr1 = 26;
stellaParser.RULE_start_Expr2 = 27;
stellaParser.RULE_start_Expr3 = 28;
stellaParser.RULE_start_Expr4 = 29;
stellaParser.RULE_start_Expr5 = 30;
stellaParser.RULE_start_Type = 31;
stellaParser.RULE_start_Type1 = 32;
stellaParser.RULE_start_Type2 = 33;
stellaParser.RULE_start_ListType = 34;
stellaParser.RULE_start_FieldType = 35;
stellaParser.RULE_start_ListFieldType = 36;
stellaParser.RULE_start_Typing = 37;
stellaParser.RULE_program = 38;
stellaParser.RULE_languageDecl = 39;
stellaParser.RULE_extension = 40;
stellaParser.RULE_listExtensionName = 41;
stellaParser.RULE_listExtension = 42;
stellaParser.RULE_decl = 43;
stellaParser.RULE_listDecl = 44;
stellaParser.RULE_localDecl = 45;
stellaParser.RULE_listLocalDecl = 46;
stellaParser.RULE_annotation = 47;
stellaParser.RULE_listAnnotation = 48;
stellaParser.RULE_paramDecl = 49;
stellaParser.RULE_listParamDecl = 50;
stellaParser.RULE_returnType = 51;
stellaParser.RULE_throwType = 52;
stellaParser.RULE_expr = 53;
stellaParser.RULE_listExpr = 54;
stellaParser.RULE_matchCase = 55;
stellaParser.RULE_listMatchCase = 56;
stellaParser.RULE_pattern = 57;
stellaParser.RULE_listPattern = 58;
stellaParser.RULE_labelledPattern = 59;
stellaParser.RULE_listLabelledPattern = 60;
stellaParser.RULE_binding = 61;
stellaParser.RULE_listBinding = 62;
stellaParser.RULE_expr0 = 63;
stellaParser.RULE_expr1 = 64;
stellaParser.RULE_expr2 = 65;
stellaParser.RULE_expr3 = 66;
stellaParser.RULE_expr4 = 67;
stellaParser.RULE_expr5 = 68;
stellaParser.RULE_type = 69;
stellaParser.RULE_type1 = 70;
stellaParser.RULE_type2 = 71;
stellaParser.RULE_listType = 72;
stellaParser.RULE_fieldType = 73;
stellaParser.RULE_listFieldType = 74;
stellaParser.RULE_typing = 75;

class Start_ProgramContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Program;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	program() {
	    return this.getTypedRuleContext(ProgramContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Program(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Program(this);
		}
	}


}



class Start_LanguageDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_LanguageDecl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	languageDecl() {
	    return this.getTypedRuleContext(LanguageDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_LanguageDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_LanguageDecl(this);
		}
	}


}



class Start_ExtensionContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Extension;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	extension() {
	    return this.getTypedRuleContext(ExtensionContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Extension(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Extension(this);
		}
	}


}



class Start_ListExtensionNameContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListExtensionName;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listExtensionName() {
	    return this.getTypedRuleContext(ListExtensionNameContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListExtensionName(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListExtensionName(this);
		}
	}


}



class Start_ListExtensionContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListExtension;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listExtension() {
	    return this.getTypedRuleContext(ListExtensionContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListExtension(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListExtension(this);
		}
	}


}



class Start_DeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Decl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	decl() {
	    return this.getTypedRuleContext(DeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Decl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Decl(this);
		}
	}


}



class Start_ListDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListDecl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listDecl() {
	    return this.getTypedRuleContext(ListDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListDecl(this);
		}
	}


}



class Start_LocalDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_LocalDecl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	localDecl() {
	    return this.getTypedRuleContext(LocalDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_LocalDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_LocalDecl(this);
		}
	}


}



class Start_ListLocalDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListLocalDecl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listLocalDecl() {
	    return this.getTypedRuleContext(ListLocalDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListLocalDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListLocalDecl(this);
		}
	}


}



class Start_AnnotationContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Annotation;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	annotation() {
	    return this.getTypedRuleContext(AnnotationContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Annotation(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Annotation(this);
		}
	}


}



class Start_ListAnnotationContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListAnnotation;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listAnnotation() {
	    return this.getTypedRuleContext(ListAnnotationContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListAnnotation(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListAnnotation(this);
		}
	}


}



class Start_ParamDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ParamDecl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	paramDecl() {
	    return this.getTypedRuleContext(ParamDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ParamDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ParamDecl(this);
		}
	}


}



class Start_ListParamDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListParamDecl;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listParamDecl() {
	    return this.getTypedRuleContext(ListParamDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListParamDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListParamDecl(this);
		}
	}


}



class Start_ReturnTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ReturnType;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	returnType() {
	    return this.getTypedRuleContext(ReturnTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ReturnType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ReturnType(this);
		}
	}


}



class Start_ThrowTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ThrowType;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	throwType() {
	    return this.getTypedRuleContext(ThrowTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ThrowType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ThrowType(this);
		}
	}


}



class Start_ExprContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr(this);
		}
	}


}



class Start_ListExprContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListExpr;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listExpr() {
	    return this.getTypedRuleContext(ListExprContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListExpr(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListExpr(this);
		}
	}


}



class Start_MatchCaseContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_MatchCase;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	matchCase() {
	    return this.getTypedRuleContext(MatchCaseContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_MatchCase(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_MatchCase(this);
		}
	}


}



class Start_ListMatchCaseContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListMatchCase;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listMatchCase() {
	    return this.getTypedRuleContext(ListMatchCaseContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListMatchCase(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListMatchCase(this);
		}
	}


}



class Start_PatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Pattern;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	pattern() {
	    return this.getTypedRuleContext(PatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Pattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Pattern(this);
		}
	}


}



class Start_ListPatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListPattern;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listPattern() {
	    return this.getTypedRuleContext(ListPatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListPattern(this);
		}
	}


}



class Start_LabelledPatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_LabelledPattern;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	labelledPattern() {
	    return this.getTypedRuleContext(LabelledPatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_LabelledPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_LabelledPattern(this);
		}
	}


}



class Start_ListLabelledPatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListLabelledPattern;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listLabelledPattern() {
	    return this.getTypedRuleContext(ListLabelledPatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListLabelledPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListLabelledPattern(this);
		}
	}


}



class Start_BindingContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Binding;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	binding() {
	    return this.getTypedRuleContext(BindingContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Binding(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Binding(this);
		}
	}


}



class Start_ListBindingContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListBinding;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listBinding() {
	    return this.getTypedRuleContext(ListBindingContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListBinding(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListBinding(this);
		}
	}


}



class Start_Expr0Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr0;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr0() {
	    return this.getTypedRuleContext(Expr0Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr0(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr0(this);
		}
	}


}



class Start_Expr1Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr1;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr1() {
	    return this.getTypedRuleContext(Expr1Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr1(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr1(this);
		}
	}


}



class Start_Expr2Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr2;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr2() {
	    return this.getTypedRuleContext(Expr2Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr2(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr2(this);
		}
	}


}



class Start_Expr3Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr3;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr3() {
	    return this.getTypedRuleContext(Expr3Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr3(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr3(this);
		}
	}


}



class Start_Expr4Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr4;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr4() {
	    return this.getTypedRuleContext(Expr4Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr4(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr4(this);
		}
	}


}



class Start_Expr5Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Expr5;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	expr5() {
	    return this.getTypedRuleContext(Expr5Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Expr5(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Expr5(this);
		}
	}


}



class Start_TypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Type;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Type(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Type(this);
		}
	}


}



class Start_Type1Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Type1;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	type1() {
	    return this.getTypedRuleContext(Type1Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Type1(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Type1(this);
		}
	}


}



class Start_Type2Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Type2;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	type2() {
	    return this.getTypedRuleContext(Type2Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Type2(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Type2(this);
		}
	}


}



class Start_ListTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListType;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listType() {
	    return this.getTypedRuleContext(ListTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListType(this);
		}
	}


}



class Start_FieldTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_FieldType;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	fieldType() {
	    return this.getTypedRuleContext(FieldTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_FieldType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_FieldType(this);
		}
	}


}



class Start_ListFieldTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_ListFieldType;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	listFieldType() {
	    return this.getTypedRuleContext(ListFieldTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_ListFieldType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_ListFieldType(this);
		}
	}


}



class Start_TypingContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_start_Typing;
        this.result = null
        this.x = null;
    }

	EOF() {
	    return this.getToken(stellaParser.EOF, 0);
	};

	typing() {
	    return this.getTypedRuleContext(TypingContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterStart_Typing(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitStart_Typing(this);
		}
	}


}



class ProgramContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_program;
        this.result = null
        this.p_1_1 = null;
        this.p_1_2 = null;
        this.p_1_3 = null;
    }

	languageDecl() {
	    return this.getTypedRuleContext(LanguageDeclContext,0);
	};

	listExtension() {
	    return this.getTypedRuleContext(ListExtensionContext,0);
	};

	listDecl() {
	    return this.getTypedRuleContext(ListDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterProgram(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitProgram(this);
		}
	}


}



class LanguageDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_languageDecl;
        this.result = null
    }

	Surrogate_id_SYMB_43() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_43, 0);
	};

	Surrogate_id_SYMB_33() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_33, 0);
	};

	Surrogate_id_SYMB_0() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_0, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterLanguageDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitLanguageDecl(this);
		}
	}


}



class ExtensionContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_extension;
        this.result = null
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_35() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_35, 0);
	};

	Surrogate_id_SYMB_58() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_58, 0);
	};

	listExtensionName() {
	    return this.getTypedRuleContext(ListExtensionNameContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExtension(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExtension(this);
		}
	}


}



class ListExtensionNameContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listExtensionName;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	ExtensionName() {
	    return this.getToken(stellaParser.ExtensionName, 0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listExtensionName() {
	    return this.getTypedRuleContext(ListExtensionNameContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListExtensionName(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListExtensionName(this);
		}
	}


}



class ListExtensionContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listExtension;
        this.result = null
        this.p_2_1 = null;
        this.p_2_2 = null;
    }

	Surrogate_id_SYMB_0() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_0, 0);
	};

	listExtension() {
	    return this.getTypedRuleContext(ListExtensionContext,0);
	};

	extension() {
	    return this.getTypedRuleContext(ExtensionContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListExtension(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListExtension(this);
		}
	}


}



class DeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_decl;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
        this.p_1_5 = null;
        this.p_1_7 = null;
        this.p_1_8 = null;
        this.p_1_10 = null;
        this.p_1_12 = null;
        this.p_2_2 = null;
        this.p_2_4 = null;
    }

	Surrogate_id_SYMB_38() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_38, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	Surrogate_id_SYMB_4() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_4, 0);
	};

	Surrogate_id_SYMB_49() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_49, 0);
	};

	Surrogate_id_SYMB_0() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_0, 0);
	};

	Surrogate_id_SYMB_5() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_5, 0);
	};

	listAnnotation() {
	    return this.getTypedRuleContext(ListAnnotationContext,0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	listParamDecl() {
	    return this.getTypedRuleContext(ListParamDeclContext,0);
	};

	returnType() {
	    return this.getTypedRuleContext(ReturnTypeContext,0);
	};

	throwType() {
	    return this.getTypedRuleContext(ThrowTypeContext,0);
	};

	listDecl() {
	    return this.getTypedRuleContext(ListDeclContext,0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	Surrogate_id_SYMB_55() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_55, 0);
	};

	Surrogate_id_SYMB_6() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_6, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitDecl(this);
		}
	}


}



class ListDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listDecl;
        this.result = null
        this.p_2_1 = null;
        this.p_2_2 = null;
    }

	listDecl() {
	    return this.getTypedRuleContext(ListDeclContext,0);
	};

	decl() {
	    return this.getTypedRuleContext(DeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListDecl(this);
		}
	}


}



class LocalDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_localDecl;
        this.result = null
        this.p_1_1 = null;
    }

	decl() {
	    return this.getTypedRuleContext(DeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterLocalDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitLocalDecl(this);
		}
	}


}



class ListLocalDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listLocalDecl;
        this.result = null
        this.p_2_1 = null;
        this.p_2_2 = null;
    }

	Surrogate_id_SYMB_0() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_0, 0);
	};

	listLocalDecl() {
	    return this.getTypedRuleContext(ListLocalDeclContext,0);
	};

	localDecl() {
	    return this.getTypedRuleContext(LocalDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListLocalDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListLocalDecl(this);
		}
	}


}



class AnnotationContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_annotation;
        this.result = null
    }

	Surrogate_id_SYMB_42() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_42, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterAnnotation(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitAnnotation(this);
		}
	}


}



class ListAnnotationContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listAnnotation;
        this.result = null
        this.p_2_1 = null;
        this.p_2_2 = null;
    }

	listAnnotation() {
	    return this.getTypedRuleContext(ListAnnotationContext,0);
	};

	annotation() {
	    return this.getTypedRuleContext(AnnotationContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListAnnotation(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListAnnotation(this);
		}
	}


}



class ParamDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_paramDecl;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_7() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_7, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterParamDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitParamDecl(this);
		}
	}


}



class ListParamDeclContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listParamDecl;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	paramDecl() {
	    return this.getTypedRuleContext(ParamDeclContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listParamDecl() {
	    return this.getTypedRuleContext(ListParamDeclContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListParamDecl(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListParamDecl(this);
		}
	}


}



class ReturnTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_returnType;
        this.result = null
        this.p_2_2 = null;
    }

	Surrogate_id_SYMB_8() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_8, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterReturnType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitReturnType(this);
		}
	}


}



class ThrowTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_throwType;
        this.result = null
        this.p_2_2 = null;
    }

	Surrogate_id_SYMB_53() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_53, 0);
	};

	listType() {
	    return this.getTypedRuleContext(ListTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterThrowType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitThrowType(this);
		}
	}


}



class ExprContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr;
        this.result = null
        this.p_1_2 = null;
        this.p_1_4 = null;
        this.p_1_6 = null;
        this.p_2_2 = null;
        this.p_2_4 = null;
        this.p_2_6 = null;
        this.p_3_1 = null;
    }

	Surrogate_id_SYMB_40() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_40, 0);
	};

	Surrogate_id_SYMB_52() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_52, 0);
	};

	Surrogate_id_SYMB_34() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_34, 0);
	};

	expr = function(i) {
	    if(i===undefined) {
	        i = null;
	    }
	    if(i===null) {
	        return this.getTypedRuleContexts(ExprContext);
	    } else {
	        return this.getTypedRuleContext(ExprContext,i);
	    }
	};

	Surrogate_id_SYMB_44() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_44, 0);
	};

	Surrogate_id_SYMB_6() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_6, 0);
	};

	Surrogate_id_SYMB_41() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_41, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	expr1() {
	    return this.getTypedRuleContext(Expr1Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr(this);
		}
	}


}



class ListExprContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listExpr;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listExpr() {
	    return this.getTypedRuleContext(ListExprContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListExpr(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListExpr(this);
		}
	}


}



class MatchCaseContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_matchCase;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_9() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_9, 0);
	};

	pattern() {
	    return this.getTypedRuleContext(PatternContext,0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterMatchCase(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitMatchCase(this);
		}
	}


}



class ListMatchCaseContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listMatchCase;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	matchCase() {
	    return this.getTypedRuleContext(MatchCaseContext,0);
	};

	Surrogate_id_SYMB_0() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_0, 0);
	};

	listMatchCase() {
	    return this.getTypedRuleContext(ListMatchCaseContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListMatchCase(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListMatchCase(this);
		}
	}


}



class PatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_pattern;
        this.result = null
        this.p_1_2 = null;
        this.p_1_4 = null;
        this.p_2_2 = null;
        this.p_3_3 = null;
        this.p_4_2 = null;
        this.p_5_3 = null;
        this.p_5_5 = null;
        this.p_8_1 = null;
        this.p_9_3 = null;
        this.p_10_1 = null;
        this.p_11_2 = null;
    }

	Surrogate_id_SYMB_10() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_10, 0);
	};

	Surrogate_id_SYMB_6() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_6, 0);
	};

	Surrogate_id_SYMB_11() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_11, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	pattern = function(i) {
	    if(i===undefined) {
	        i = null;
	    }
	    if(i===null) {
	        return this.getTypedRuleContexts(PatternContext);
	    } else {
	        return this.getTypedRuleContext(PatternContext,i);
	    }
	};

	Surrogate_id_SYMB_4() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_4, 0);
	};

	Surrogate_id_SYMB_5() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_5, 0);
	};

	listPattern() {
	    return this.getTypedRuleContext(ListPatternContext,0);
	};

	Surrogate_id_SYMB_48() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_48, 0);
	};

	listLabelledPattern() {
	    return this.getTypedRuleContext(ListLabelledPatternContext,0);
	};

	Surrogate_id_SYMB_12() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_12, 0);
	};

	Surrogate_id_SYMB_13() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_13, 0);
	};

	Surrogate_id_SYMB_32() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_32, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	Surrogate_id_SYMB_36() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_36, 0);
	};

	Surrogate_id_SYMB_54() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_54, 0);
	};

	INTEGER() {
	    return this.getToken(stellaParser.INTEGER, 0);
	};

	Surrogate_id_SYMB_51() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_51, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitPattern(this);
		}
	}


}



class ListPatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listPattern;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	pattern() {
	    return this.getTypedRuleContext(PatternContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listPattern() {
	    return this.getTypedRuleContext(ListPatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListPattern(this);
		}
	}


}



class LabelledPatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_labelledPattern;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_6() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_6, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	pattern() {
	    return this.getTypedRuleContext(PatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterLabelledPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitLabelledPattern(this);
		}
	}


}



class ListLabelledPatternContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listLabelledPattern;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	labelledPattern() {
	    return this.getTypedRuleContext(LabelledPatternContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listLabelledPattern() {
	    return this.getTypedRuleContext(ListLabelledPatternContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListLabelledPattern(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListLabelledPattern(this);
		}
	}


}



class BindingContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_binding;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_6() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_6, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterBinding(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitBinding(this);
		}
	}


}



class ListBindingContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listBinding;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	binding() {
	    return this.getTypedRuleContext(BindingContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listBinding() {
	    return this.getTypedRuleContext(ListBindingContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListBinding(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListBinding(this);
		}
	}


}



class Expr0Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr0;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
        this.p_2_1 = null;
        this.p_2_3 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
        this.p_4_1 = null;
        this.p_4_3 = null;
        this.p_5_1 = null;
        this.p_5_3 = null;
        this.p_6_1 = null;
        this.p_6_3 = null;
    }

	Surrogate_id_SYMB_10() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_10, 0);
	};

	expr1 = function(i) {
	    if(i===undefined) {
	        i = null;
	    }
	    if(i===null) {
	        return this.getTypedRuleContexts(Expr1Context);
	    } else {
	        return this.getTypedRuleContext(Expr1Context,i);
	    }
	};

	Surrogate_id_SYMB_14() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_14, 0);
	};

	Surrogate_id_SYMB_11() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_11, 0);
	};

	Surrogate_id_SYMB_15() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_15, 0);
	};

	Surrogate_id_SYMB_16() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_16, 0);
	};

	Surrogate_id_SYMB_17() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_17, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr0(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr0(this);
		}
	}


}



class Expr1Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr1;
        this.result = null
        this.p_1_1 = null;
        this.p_8_1 = null;
        this.p_9_1 = null;
        this.p_2_3 = null;
        this.p_2_7 = null;
        this.p_3_2 = null;
        this.p_4_3 = null;
        this.p_5_2 = null;
        this.p_5_4 = null;
        this.p_6_2 = null;
        this.p_6_4 = null;
        this.p_7_2 = null;
        this.p_10_1 = null;
        this.p_1_3 = null;
        this.p_8_3 = null;
        this.p_9_3 = null;
    }

	Surrogate_id_SYMB_38() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_38, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	Surrogate_id_SYMB_4() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_4, 0);
	};

	Surrogate_id_SYMB_49() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_49, 0);
	};

	Surrogate_id_SYMB_0() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_0, 0);
	};

	Surrogate_id_SYMB_5() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_5, 0);
	};

	listParamDecl() {
	    return this.getTypedRuleContext(ListParamDeclContext,0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	listExpr() {
	    return this.getTypedRuleContext(ListExprContext,0);
	};

	Surrogate_id_SYMB_48() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_48, 0);
	};

	listBinding() {
	    return this.getTypedRuleContext(ListBindingContext,0);
	};

	Surrogate_id_SYMB_10() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_10, 0);
	};

	Surrogate_id_SYMB_6() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_6, 0);
	};

	Surrogate_id_SYMB_11() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_11, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	Surrogate_id_SYMB_45() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_45, 0);
	};

	expr1() {
	    return this.getTypedRuleContext(Expr1Context,0);
	};

	listMatchCase() {
	    return this.getTypedRuleContext(ListMatchCaseContext,0);
	};

	Surrogate_id_SYMB_12() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_12, 0);
	};

	Surrogate_id_SYMB_13() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_13, 0);
	};

	expr2() {
	    return this.getTypedRuleContext(Expr2Context,0);
	};

	Surrogate_id_SYMB_31() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_31, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	Surrogate_id_SYMB_18() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_18, 0);
	};

	Surrogate_id_SYMB_47() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_47, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr1(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr1(this);
		}
	}


}



class Expr2Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr2;
        this.result = null
        this.p_1_1 = null;
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_1_3 = null;
        this.p_2_3 = null;
    }

	expr3() {
	    return this.getTypedRuleContext(Expr3Context,0);
	};

	Surrogate_id_SYMB_19() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_19, 0);
	};

	expr2() {
	    return this.getTypedRuleContext(Expr2Context,0);
	};

	Surrogate_id_SYMB_30() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_30, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr2(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr2(this);
		}
	}


}



class Expr3Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr3;
        this.result = null
        this.p_1_1 = null;
        this.p_2_1 = null;
        this.p_1_3 = null;
    }

	expr4() {
	    return this.getTypedRuleContext(Expr4Context,0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	expr3() {
	    return this.getTypedRuleContext(Expr3Context,0);
	};

	listExpr() {
	    return this.getTypedRuleContext(ListExprContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr3(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr3(this);
		}
	}


}



class Expr4Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr4;
        this.result = null
        this.p_1_3 = null;
        this.p_1_5 = null;
        this.p_2_3 = null;
        this.p_3_3 = null;
        this.p_4_3 = null;
        this.p_5_3 = null;
        this.p_6_3 = null;
        this.p_7_3 = null;
        this.p_8_3 = null;
        this.p_9_3 = null;
        this.p_10_3 = null;
        this.p_10_5 = null;
        this.p_10_7 = null;
        this.p_11_3 = null;
        this.p_11_5 = null;
        this.p_12_3 = null;
        this.p_12_5 = null;
        this.p_13_1 = null;
    }

	Surrogate_id_SYMB_32() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_32, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_1 = function(i) {
		if(i===undefined) {
			i = null;
		}
	    if(i===null) {
	        return this.getTokens(stellaParser.Surrogate_id_SYMB_1);
	    } else {
	        return this.getToken(stellaParser.Surrogate_id_SYMB_1, i);
	    }
	};


	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	expr = function(i) {
	    if(i===undefined) {
	        i = null;
	    }
	    if(i===null) {
	        return this.getTypedRuleContexts(ExprContext);
	    } else {
	        return this.getTypedRuleContext(ExprContext,i);
	    }
	};

	Surrogate_id_SYMB_20() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_20, 0);
	};

	Surrogate_id_SYMB_21() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_21, 0);
	};

	Surrogate_id_SYMB_22() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_22, 0);
	};

	Surrogate_id_SYMB_51() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_51, 0);
	};

	Surrogate_id_SYMB_46() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_46, 0);
	};

	Surrogate_id_SYMB_23() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_23, 0);
	};

	Surrogate_id_SYMB_24() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_24, 0);
	};

	Surrogate_id_SYMB_37() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_37, 0);
	};

	Surrogate_id_SYMB_25() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_25, 0);
	};

	Surrogate_id_SYMB_39() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_39, 0);
	};

	Surrogate_id_SYMB_12() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_12, 0);
	};

	Surrogate_id_SYMB_13() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_13, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	expr5() {
	    return this.getTypedRuleContext(Expr5Context,0);
	};

	Surrogate_id_SYMB_56() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_56, 0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr4(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr4(this);
		}
	}


}



class Expr5Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_expr5;
        this.result = null
        this.p_1_1 = null;
        this.p_2_1 = null;
        this.p_5_1 = null;
        this.p_6_1 = null;
        this.p_7_2 = null;
        this.p_1_3 = null;
        this.p_2_3 = null;
    }

	Surrogate_id_SYMB_54() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_54, 0);
	};

	Surrogate_id_SYMB_36() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_36, 0);
	};

	INTEGER() {
	    return this.getToken(stellaParser.INTEGER, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	Surrogate_id_SYMB_26() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_26, 0);
	};

	expr5() {
	    return this.getTypedRuleContext(Expr5Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterExpr5(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitExpr5(this);
		}
	}


}



class TypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_type;
        this.result = null
        this.p_1_3 = null;
        this.p_1_6 = null;
        this.p_2_2 = null;
        this.p_2_4 = null;
        this.p_3_1 = null;
    }

	Surrogate_id_SYMB_38() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_38, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	Surrogate_id_SYMB_8() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_8, 0);
	};

	listType() {
	    return this.getTypedRuleContext(ListTypeContext,0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	Surrogate_id_SYMB_59() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_59, 0);
	};

	Surrogate_id_SYMB_26() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_26, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	type1() {
	    return this.getTypedRuleContext(Type1Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitType(this);
		}
	}


}



class Type1Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_type1;
        this.result = null
        this.p_1_2 = null;
        this.p_2_3 = null;
        this.p_3_3 = null;
        this.p_4_2 = null;
        this.p_5_1 = null;
    }

	Surrogate_id_SYMB_4() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_4, 0);
	};

	Surrogate_id_SYMB_5() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_5, 0);
	};

	listType() {
	    return this.getTypedRuleContext(ListTypeContext,0);
	};

	Surrogate_id_SYMB_50() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_50, 0);
	};

	listFieldType() {
	    return this.getTypedRuleContext(ListFieldTypeContext,0);
	};

	Surrogate_id_SYMB_57() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_57, 0);
	};

	Surrogate_id_SYMB_10() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_10, 0);
	};

	Surrogate_id_SYMB_11() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_11, 0);
	};

	Surrogate_id_SYMB_12() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_12, 0);
	};

	Surrogate_id_SYMB_13() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_13, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	type2() {
	    return this.getTypedRuleContext(Type2Context,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterType1(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitType1(this);
		}
	}


}



class Type2Context extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_type2;
        this.result = null
        this.p_4_1 = null;
        this.p_5_2 = null;
    }

	Surrogate_id_SYMB_27() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_27, 0);
	};

	Surrogate_id_SYMB_28() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_28, 0);
	};

	Surrogate_id_SYMB_29() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_29, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	Surrogate_id_SYMB_2() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_2, 0);
	};

	Surrogate_id_SYMB_3() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_3, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterType2(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitType2(this);
		}
	}


}



class ListTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listType;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listType() {
	    return this.getTypedRuleContext(ListTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListType(this);
		}
	}


}



class FieldTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_fieldType;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_7() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_7, 0);
	};

	StellaIdent() {
	    return this.getToken(stellaParser.StellaIdent, 0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterFieldType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitFieldType(this);
		}
	}


}



class ListFieldTypeContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_listFieldType;
        this.result = null
        this.p_2_1 = null;
        this.p_3_1 = null;
        this.p_3_3 = null;
    }

	fieldType() {
	    return this.getTypedRuleContext(FieldTypeContext,0);
	};

	Surrogate_id_SYMB_1() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_1, 0);
	};

	listFieldType() {
	    return this.getTypedRuleContext(ListFieldTypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterListFieldType(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitListFieldType(this);
		}
	}


}



class TypingContext extends antlr4.ParserRuleContext {

    constructor(parser, parent, invokingState) {
        if(parent===undefined) {
            parent = null;
        }
        if(invokingState===undefined || invokingState===null) {
            invokingState = -1;
        }
        super(parent, invokingState);
        this.parser = parser;
        this.ruleIndex = stellaParser.RULE_typing;
        this.result = null
        this.p_1_1 = null;
        this.p_1_3 = null;
    }

	Surrogate_id_SYMB_7() {
	    return this.getToken(stellaParser.Surrogate_id_SYMB_7, 0);
	};

	expr() {
	    return this.getTypedRuleContext(ExprContext,0);
	};

	type() {
	    return this.getTypedRuleContext(TypeContext,0);
	};

	enterRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.enterTyping(this);
		}
	}

	exitRule(listener) {
	    if(listener instanceof stellaParserListener ) {
	        listener.exitTyping(this);
		}
	}


}




stellaParser.Start_ProgramContext = Start_ProgramContext; 
stellaParser.Start_LanguageDeclContext = Start_LanguageDeclContext; 
stellaParser.Start_ExtensionContext = Start_ExtensionContext; 
stellaParser.Start_ListExtensionNameContext = Start_ListExtensionNameContext; 
stellaParser.Start_ListExtensionContext = Start_ListExtensionContext; 
stellaParser.Start_DeclContext = Start_DeclContext; 
stellaParser.Start_ListDeclContext = Start_ListDeclContext; 
stellaParser.Start_LocalDeclContext = Start_LocalDeclContext; 
stellaParser.Start_ListLocalDeclContext = Start_ListLocalDeclContext; 
stellaParser.Start_AnnotationContext = Start_AnnotationContext; 
stellaParser.Start_ListAnnotationContext = Start_ListAnnotationContext; 
stellaParser.Start_ParamDeclContext = Start_ParamDeclContext; 
stellaParser.Start_ListParamDeclContext = Start_ListParamDeclContext; 
stellaParser.Start_ReturnTypeContext = Start_ReturnTypeContext; 
stellaParser.Start_ThrowTypeContext = Start_ThrowTypeContext; 
stellaParser.Start_ExprContext = Start_ExprContext; 
stellaParser.Start_ListExprContext = Start_ListExprContext; 
stellaParser.Start_MatchCaseContext = Start_MatchCaseContext; 
stellaParser.Start_ListMatchCaseContext = Start_ListMatchCaseContext; 
stellaParser.Start_PatternContext = Start_PatternContext; 
stellaParser.Start_ListPatternContext = Start_ListPatternContext; 
stellaParser.Start_LabelledPatternContext = Start_LabelledPatternContext; 
stellaParser.Start_ListLabelledPatternContext = Start_ListLabelledPatternContext; 
stellaParser.Start_BindingContext = Start_BindingContext; 
stellaParser.Start_ListBindingContext = Start_ListBindingContext; 
stellaParser.Start_Expr0Context = Start_Expr0Context; 
stellaParser.Start_Expr1Context = Start_Expr1Context; 
stellaParser.Start_Expr2Context = Start_Expr2Context; 
stellaParser.Start_Expr3Context = Start_Expr3Context; 
stellaParser.Start_Expr4Context = Start_Expr4Context; 
stellaParser.Start_Expr5Context = Start_Expr5Context; 
stellaParser.Start_TypeContext = Start_TypeContext; 
stellaParser.Start_Type1Context = Start_Type1Context; 
stellaParser.Start_Type2Context = Start_Type2Context; 
stellaParser.Start_ListTypeContext = Start_ListTypeContext; 
stellaParser.Start_FieldTypeContext = Start_FieldTypeContext; 
stellaParser.Start_ListFieldTypeContext = Start_ListFieldTypeContext; 
stellaParser.Start_TypingContext = Start_TypingContext; 
stellaParser.ProgramContext = ProgramContext; 
stellaParser.LanguageDeclContext = LanguageDeclContext; 
stellaParser.ExtensionContext = ExtensionContext; 
stellaParser.ListExtensionNameContext = ListExtensionNameContext; 
stellaParser.ListExtensionContext = ListExtensionContext; 
stellaParser.DeclContext = DeclContext; 
stellaParser.ListDeclContext = ListDeclContext; 
stellaParser.LocalDeclContext = LocalDeclContext; 
stellaParser.ListLocalDeclContext = ListLocalDeclContext; 
stellaParser.AnnotationContext = AnnotationContext; 
stellaParser.ListAnnotationContext = ListAnnotationContext; 
stellaParser.ParamDeclContext = ParamDeclContext; 
stellaParser.ListParamDeclContext = ListParamDeclContext; 
stellaParser.ReturnTypeContext = ReturnTypeContext; 
stellaParser.ThrowTypeContext = ThrowTypeContext; 
stellaParser.ExprContext = ExprContext; 
stellaParser.ListExprContext = ListExprContext; 
stellaParser.MatchCaseContext = MatchCaseContext; 
stellaParser.ListMatchCaseContext = ListMatchCaseContext; 
stellaParser.PatternContext = PatternContext; 
stellaParser.ListPatternContext = ListPatternContext; 
stellaParser.LabelledPatternContext = LabelledPatternContext; 
stellaParser.ListLabelledPatternContext = ListLabelledPatternContext; 
stellaParser.BindingContext = BindingContext; 
stellaParser.ListBindingContext = ListBindingContext; 
stellaParser.Expr0Context = Expr0Context; 
stellaParser.Expr1Context = Expr1Context; 
stellaParser.Expr2Context = Expr2Context; 
stellaParser.Expr3Context = Expr3Context; 
stellaParser.Expr4Context = Expr4Context; 
stellaParser.Expr5Context = Expr5Context; 
stellaParser.TypeContext = TypeContext; 
stellaParser.Type1Context = Type1Context; 
stellaParser.Type2Context = Type2Context; 
stellaParser.ListTypeContext = ListTypeContext; 
stellaParser.FieldTypeContext = FieldTypeContext; 
stellaParser.ListFieldTypeContext = ListFieldTypeContext; 
stellaParser.TypingContext = TypingContext; 
