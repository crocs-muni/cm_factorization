import time
import math
import argparse
import os
import re
import gc
import shutil
import sys
import functools
import random
import sympy.ntheory as nt
import json
import logging
import glob
import numpy
import itertools
import collections
import coloredlogs
import traceback
import resource
import subprocess
from six.moves import range

from sage.misc.sage_timeit import SageTimeitResult
from sage.misc.sage_timeit import sage_timeit
from sage.misc.prandom import randrange
from sage.rings.number_field.number_field_ideal import NumberFieldFractionalIdeal
from sage.parallel.decorate import fork


# https://pypi.org/project/memory-profiler/
# https://github.com/jmdana/memprof
# from memory_profiler import profile
# from memprof import memprof

# packages:
# pip install coloredlogs memprof memory_profiler py-cpuinfo psutil backports.tempfile pyunpack

# test with:
# ../SageMathDeb9/sage ../copp/suspi_5.sage --action batchgcd --data-dir ../cards_hsms/  --random-keys-struct '[{"bits":512,  "n":10}, {"bits":256,  "n":10}, {"bits":1024, "n":10}, {"bits":512, "type":"cm", "n":10, "d":19}]'


debug = False
logger = logging.getLogger(__name__)
coloredlogs.CHROOT_FILES = []
coloredlogs.install(level=logging.DEBUG, use_chroot=False)


UNDEF_RESULTS = ['NO DATA (timed out)', 'NO DATA', 'INVALID DATA', 'INVALID DATA ', None]


# discriminants
Ds = [3, 4, 7, 8, 11, 19, 43, 67, 163, 15, 20, 24, 35, 40, 51, 52, 88, 91, 115, 123, 148, 187, 232, 235, 267, 403, 427, 23, 31, 59, 83, 107, 139, 211, 283, 307, 331, 379, 499, 547, 643, 883, 907, 39, 55, 56, 68, 84, 120, 132, 136, 155, 168, 184, 195, 203, 219, 228, 259, 280, 291, 292, 312, 323, 328, 340, 355, 372, 388, 408, 435, 483, 520, 532, 555, 568, 595, 627, 667, 708, 715, 723, 760, 763, 772, 795, 955, 1003, 1012, 1027, 1227, 1243, 1387, 1411, 1435, 1507, 1555,47, 79, 103, 127, 131, 179, 227, 347, 443, 523, 571, 619, 683, 691, 739, 787, 947, 1051, 1123, 1723, 1747, 1867, 2203, 2347, 2683,87, 104, 116, 152, 212, 244, 247, 339, 411, 424, 436, 451, 472, 515, 628, 707, 771, 808, 835, 843, 856, 1048, 1059, 1099, 1108, 1147, 1192, 1203, 1219, 1267, 1315, 1347, 1363, 1432, 1563, 1588, 1603, 1843, 1915, 1963, 2227, 2283, 2443, 2515, 2563, 2787, 2923, 3235, 3427, 3523, 3763, 71, 151, 223, 251, 463, 467, 487, 587, 811, 827, 859, 1163, 1171, 1483, 1523, 1627, 1787, 1987, 2011, 2083, 2179, 2251, 2467, 2707, 3019, 3067, 3187, 3907, 4603, 5107, 5923, 95, 111, 164, 183, 248, 260, 264, 276, 295, 299, 308, 371, 376, 395, 420, 452, 456, 548, 552, 564, 579, 580, 583, 616, 632, 651, 660, 712, 820, 840, 852, 868, 904, 915, 939, 952, 979, 987, 995, 1032, 1043, 1060, 1092, 1128, 1131, 1155, 1195, 1204, 1240, 1252, 1288, 1299, 1320, 1339, 1348, 1380, 1428, 1443, 1528, 1540, 1635, 1651, 1659, 1672, 1731, 1752, 1768, 1771, 1780, 1795, 1803, 1828, 1848, 1864, 1912, 1939, 1947, 1992, 1995, 2020, 2035, 2059, 2067, 2139, 2163, 2212, 2248, 2307, 2308, 2323, 2392, 2395, 2419, 2451, 2587, 2611, 2632, 2667, 2715, 2755, 2788, 2827, 2947, 2968, 2995, 3003, 3172, 3243, 3315, 3355, 3403, 3448, 3507, 3595, 3787, 3883, 3963, 4123, 4195, 4267, 4323, 4387, 4747, 4843, 4867, 5083, 5467, 5587, 5707, 5947, 6307, 199, 367, 419, 491, 563, 823, 1087, 1187, 1291, 1423, 1579, 2003, 2803, 3163, 3259, 3307, 3547, 3643, 4027, 4243, 4363, 4483, 4723, 4987, 5443, 6043, 6427, 6763, 6883, 7723, 8563, 8803, 9067, 10627, 119, 143, 159, 296, 303, 319, 344, 415, 488, 611, 635, 664, 699, 724, 779, 788, 803, 851, 872, 916, 923, 1115, 1268, 1384, 1492, 1576, 1643, 1684, 1688, 1707, 1779, 1819, 1835, 1891, 1923, 2152, 2164, 2363, 2452, 2643, 2776, 2836, 2899, 3028, 3091, 3139, 3147, 3291, 3412, 3508, 3635, 3667, 3683, 3811, 3859, 3928, 4083, 4227, 4372, 4435, 4579, 4627, 4852, 4915, 5131, 5163, 5272, 5515, 5611, 5667, 5803, 6115, 6259, 6403, 6667, 7123, 7363, 7387, 7435, 7483, 7627, 8227, 8947, 9307, 10147, 10483, 13843, 167, 271, 659, 967, 1283, 1303, 1307, 1459, 1531, 1699, 2027, 2267, 2539, 2731, 2851, 2971, 3203, 3347, 3499, 3739, 3931, 4051, 5179, 5683, 6163, 6547, 7027, 7507, 7603, 7867, 8443, 9283, 9403, 9643, 9787, 10987, 13003, 13267, 14107, 14683, 15667, 231, 255, 327, 356, 440, 516, 543, 655, 680, 687, 696, 728, 731, 744, 755, 804, 888, 932, 948, 964, 984, 996, 1011, 1067, 1096, 1144, 1208, 1235, 1236, 1255, 1272, 1336, 1355, 1371, 1419, 1464, 1480, 1491, 1515, 1547, 1572, 1668, 1720, 1732, 1763, 1807, 1812, 1892, 1955, 1972, 2068, 2091, 2104, 2132, 2148, 2155, 2235, 2260, 2355, 2387, 2388, 2424, 2440, 2468, 2472, 2488, 2491, 2555, 2595, 2627, 2635, 2676, 2680, 2692, 2723, 2728, 2740, 2795, 2867, 2872, 2920, 2955, 3012, 3027, 3043, 3048, 3115, 3208, 3252, 3256, 3268, 3304, 3387, 3451, 3459, 3592, 3619, 3652, 3723, 3747, 3768, 3796, 3835, 3880, 3892, 3955, 3972, 4035, 4120, 4132, 4147, 4152, 4155, 4168, 4291, 4360, 4411, 4467, 4531, 4552, 4555, 4587, 4648, 4699, 4708, 4755, 4771, 4792, 4795, 4827, 4888, 4907, 4947, 4963, 5032, 5035, 5128, 5140, 5155, 5188, 5259, 5299, 5307, 5371, 5395, 5523, 5595, 5755, 5763, 5811, 5835, 6187, 6232, 6235, 6267, 6283, 6472, 6483, 6603, 6643, 6715, 6787, 6843, 6931, 6955, 6963, 6987, 7107, 7291, 7492, 7555, 7683, 7891, 7912, 8068, 8131, 8155, 8248, 8323, 8347, 8395, 8787, 8827, 9003, 9139, 9355, 9523, 9667, 9843, 10003, 10603, 10707, 10747, 10795, 10915, 11155, 11347, 11707, 11803, 12307, 12643, 14443, 15163, 15283, 16003, 17803, 191, 263, 607, 631, 727, 1019, 1451, 1499, 1667, 1907, 2131, 2143, 2371, 2659, 2963, 3083, 3691, 4003, 4507, 4643, 5347, 5419, 5779, 6619, 7243, 7963, 9547, 9739, 11467, 11587, 11827, 11923, 12043, 14347, 15787, 16963, 20563, 215, 287, 391, 404, 447, 511, 535, 536, 596, 692, 703, 807, 899, 1112, 1211, 1396, 1403, 1527, 1816, 1851, 1883, 2008, 2123, 2147, 2171, 2335, 2427, 2507, 2536, 2571, 2612, 2779, 2931, 2932, 3112, 3227, 3352, 3579, 3707, 3715, 3867, 3988, 4187, 4315, 4443, 4468, 4659, 4803, 4948, 5027, 5091, 5251, 5267, 5608, 5723, 5812, 5971, 6388, 6499, 6523, 6568, 6979, 7067, 7099, 7147, 7915, 8035, 8187, 8611, 8899, 9115, 9172, 9235, 9427, 10123, 10315, 10363, 10411, 11227, 12147, 12667, 12787, 13027, 13435, 13483, 13603, 14203, 16867, 18187, 18547, 18643, 20227, 21547, 23083, 30067, 239, 439, 751, 971, 1259, 1327, 1427, 1567, 1619, 2243, 2647, 2699, 2843, 3331, 3571, 3803, 4099, 4219, 5003, 5227, 5323, 5563, 5827, 5987, 6067, 6091, 6211, 6571, 7219, 7459, 7547, 8467, 8707, 8779, 9043, 9907, 10243, 10267, 10459, 10651, 10723, 11083, 11971, 12163, 12763, 13147, 13963, 14323, 14827, 14851, 15187, 15643, 15907, 16603, 16843, 17467, 17923, 18043, 18523, 19387, 19867, 20707, 22003, 26203, 27883, 29947, 32323, 34483, 	399, 407, 471, 559, 584, 644, 663, 740, 799, 884, 895, 903, 943, 1015, 1016, 1023, 1028, 1047, 1139, 1140, 1159, 1220, 1379, 1412, 1416, 1508, 1560, 1595, 1608, 1624, 1636, 1640, 1716, 1860, 1876, 1924, 1983, 2004, 2019, 2040, 2056, 2072, 2095, 2195, 2211, 2244, 2280, 2292, 2296, 2328, 2356, 2379, 2436, 2568, 2580, 2584, 2739, 2760, 2811, 2868, 2884, 2980, 3063, 3108, 3140, 3144, 3160, 3171, 3192, 3220, 3336, 3363, 3379, 3432, 3435, 3443, 3460, 3480, 3531, 3556, 3588, 3603, 3640, 3732, 3752, 3784, 3795, 3819, 3828, 3832, 3939, 3976, 4008, 4020, 4043, 4171, 4179, 4180, 4216, 4228, 4251, 4260, 4324, 4379, 4420, 4427, 4440, 4452, 4488, 4515, 4516, 4596, 4612, 4683, 4687, 4712, 4740, 4804, 4899, 4939, 4971, 4984, 5115, 5160, 5187, 5195, 5208, 5363, 5380, 5403, 5412, 5428, 5460, 5572, 5668, 5752, 5848, 5860, 5883, 5896, 5907, 5908, 5992, 5995, 6040, 6052, 6099, 6123, 6148, 6195, 6312, 6315, 6328, 6355, 6395, 6420, 6532, 6580, 6595, 6612, 6628, 6708, 6747, 6771, 6792, 6820, 6868, 6923, 6952, 7003, 7035, 7051, 7195, 7288, 7315, 7347, 7368, 7395, 7480, 7491, 7540, 7579, 7588, 7672, 7707, 7747, 7755, 7780, 7795, 7819, 7828, 7843, 7923, 7995, 8008, 8043, 8052, 8083, 8283, 8299, 8308, 8452, 8515, 8547, 8548, 8635, 8643, 8680, 8683, 8715, 8835, 8859, 8932, 8968, 9208, 9219, 9412, 9483, 9507, 9508, 9595, 9640, 9763, 9835, 9867, 9955, 10132, 10168, 10195, 10203, 10227, 10312, 10387, 10420, 10563, 10587, 10635, 10803, 10843, 10948, 10963, 11067, 11092, 11107, 11179, 11203, 11512, 11523, 11563, 11572, 11635, 11715, 11848, 11995, 12027, 12259, 12387, 12523, 12595, 12747, 12772, 12835, 12859, 12868, 13123, 13192, 13195, 13288, 13323, 13363, 13507, 13795, 13819, 13827, 14008, 14155, 14371, 14403, 14547, 14707, 14763, 14995, 15067, 15387, 15403, 15547, 15715, 16027, 16195, 16347, 16531, 16555, 16723, 17227, 17323, 17347, 17427, 17515, 18403, 18715, 18883, 18907, 19147, 19195, 19947, 19987, 20155, 20395, 21403, 21715, 21835, 22243, 22843, 23395, 23587, 24403, 25027, 25267, 27307, 27787, 28963, 31243, 383, 991, 1091, 1571, 1663, 1783, 2531, 3323, 3947, 4339, 4447, 4547, 4651, 5483, 6203, 6379, 6451, 6827, 6907, 7883, 8539, 8731, 9883, 11251, 11443, 12907, 13627, 14083, 14779, 14947, 16699, 17827, 18307, 19963, 21067, 23563, 24907, 25243, 26083, 26107, 27763, 31627, 33427, 36523, 37123, 335, 519, 527, 679, 1135, 1172, 1207, 1383, 1448, 1687, 1691, 1927, 2047, 2051, 2167, 2228, 2291, 2315, 2344, 2644, 2747, 2859, 3035, 3107, 3543, 3544, 3651, 3688, 4072, 4299, 4307, 4568, 4819, 4883, 5224, 5315, 5464, 5492, 5539, 5899, 6196, 6227, 6331, 6387, 6484, 6739, 6835, 7323, 7339, 7528, 7571, 7715, 7732, 7771, 7827, 8152, 8203, 8212, 8331, 8403, 8488, 8507, 8587, 8884, 9123, 9211, 9563, 9627, 9683, 9748, 9832, 10228, 10264, 10347, 10523, 11188, 11419, 11608, 11643, 11683, 11851, 11992, 12067, 12148, 12187, 12235, 12283, 12651, 12723, 12811, 12952, 13227, 13315, 13387, 13747, 13947, 13987, 14163, 14227, 14515, 14667, 14932, 15115, 15243, 16123, 16171, 16387, 16627, 17035, 17131, 17403, 17635, 18283, 18712, 19027, 19123, 19651, 20035, 20827, 21043, 21652, 21667, 21907, 22267, 22443, 22507, 22947, 23347, 23467, 23683, 23923, 24067, 24523, 24667, 24787, 25435, 26587, 26707, 28147, 29467, 32827, 33763, 34027, 34507, 36667, 39307, 40987, 41827, 43387, 48427, 311, 359, 919, 1063, 1543, 1831, 2099, 2339, 2459, 3343, 3463, 3467, 3607, 4019, 4139, 4327, 5059, 5147, 5527, 5659, 6803, 8419, 8923, 8971, 9619, 10891, 11299, 15091, 15331, 16363, 16747, 17011, 17299, 17539, 17683, 19507, 21187, 21211, 21283, 23203, 24763, 26227, 27043, 29803, 31123, 37507, 38707, 	455, 615, 776, 824, 836, 920, 1064, 1124, 1160, 1263, 1284, 1460, 1495, 1524, 1544, 1592, 1604, 1652, 1695, 1739, 1748, 1796, 1880, 1887, 1896, 1928, 1940, 1956, 2136, 2247, 2360, 2404, 2407, 2483, 2487, 2532, 2552, 2596, 2603, 2712, 2724, 2743, 2948, 2983, 2987, 3007, 3016, 3076, 3099, 3103, 3124, 3131, 3155, 3219, 3288, 3320, 3367, 3395, 3496, 3512, 3515, 3567, 3655, 3668, 3684, 3748, 3755, 3908, 3979, 4011, 4015, 4024, 4036, 4148, 4264, 4355, 4371, 4395, 4403, 4408, 4539, 4548, 4660, 4728, 4731, 4756, 4763, 4855, 4891, 5019, 5028, 5044, 5080, 5092, 5268, 5331, 5332, 5352, 5368, 5512, 5560, 5592, 5731, 5944, 5955, 5956, 5988, 6051, 6088, 6136, 6139, 6168, 6280, 6339, 6467, 6504, 6648, 6712, 6755, 6808, 6856, 7012, 7032, 7044, 7060, 7096, 7131, 7144, 7163, 7171, 7192, 7240, 7428, 7432, 7467, 7572, 7611, 7624, 7635, 7651, 7667, 7720, 7851, 7876, 7924, 7939, 8067, 8251, 8292, 8296, 8355, 8404, 8472, 8491, 8632, 8692, 8755, 8808, 8920, 8995, 9051, 9124, 9147, 9160, 9195, 9331, 9339, 9363, 9443, 9571, 9592, 9688, 9691, 9732, 9755, 9795, 9892, 9976, 9979, 10027, 10083, 10155, 10171, 10291, 10299, 10308, 10507, 10515, 10552, 10564, 10819, 10888, 11272, 11320, 11355, 11379, 11395, 11427, 11428, 11539, 11659, 11755, 11860, 11883, 11947, 11955, 12019, 12139, 12280, 12315, 12328, 12331, 12355, 12363, 12467, 12468, 12472, 12499, 12532, 12587, 12603, 12712, 12883, 12931, 12955, 12963, 13155, 13243, 13528, 13555, 13588, 13651, 13803, 13960, 14307, 14331, 14467, 14491, 14659, 14755, 14788, 15235, 15268, 15355, 15603, 15688, 15691, 15763, 15883, 15892, 15955, 16147, 16228, 16395, 16408, 16435, 16483, 16507, 16612, 16648, 16683, 16707, 16915, 16923, 17067, 17187, 17368, 17563, 17643, 17763, 17907, 18067, 18163, 18195, 18232, 18355, 18363, 19083, 19443, 19492, 19555, 19923, 20083, 20203, 20587, 20683, 20755, 20883, 21091, 21235, 21268, 21307, 21387, 21508, 21595, 21723, 21763, 21883, 22387, 22467, 22555, 22603, 22723, 23443, 23947, 24283, 24355, 24747, 24963, 25123, 25363, 26635, 26755, 26827, 26923, 27003, 27955, 27987, 28483, 28555, 29107, 29203, 30283, 30787, 31003, 31483, 31747, 31987, 32923, 33163, 34435, 35683, 35995, 36283, 37627, 37843, 37867, 38347, 39187, 39403, 40243, 40363, 40555, 40723, 43747, 47083, 48283, 51643, 54763, 58507, 431, 503, 743, 863, 1931, 2503, 2579, 2767, 2819, 3011, 3371, 4283, 4523, 4691, 5011, 5647, 5851, 5867, 6323, 6691, 7907, 8059, 8123, 8171, 8243, 8387, 8627, 8747, 9091, 9187, 9811, 9859, 10067, 10771, 11731, 12107, 12547, 13171, 13291, 13339, 13723, 14419, 14563, 15427, 16339, 16987, 17107, 17707, 17971, 18427, 18979, 19483, 19531, 19819, 20947, 21379, 22027, 22483, 22963, 23227, 23827, 25603, 26683, 27427, 28387, 28723, 28867, 31963, 32803, 34147, 34963, 35323, 36067, 36187, 39043, 40483, 44683, 46027, 49603, 51283, 52627, 55603, 58963, 59467, 61483, 591, 623, 767, 871, 879, 1076, 1111, 1167, 1304, 1556, 1591, 1639, 1903, 2215, 2216, 2263, 2435, 2623, 2648, 2815, 2863, 2935, 3032, 3151, 3316, 3563, 3587, 3827, 4084, 4115, 4163, 4328, 4456, 4504, 4667, 4811, 5383, 5416, 5603, 5716, 5739, 5972, 6019, 6127, 6243, 6616, 6772, 6819, 7179, 7235, 7403, 7763, 7768, 7899, 8023, 8143, 8371, 8659, 8728, 8851, 8907, 8915, 9267, 9304, 9496, 10435, 10579, 10708, 10851, 11035, 11283, 11363, 11668, 12091, 12115, 12403, 12867, 13672, 14019, 14059, 14179, 14548, 14587, 14635, 15208, 15563, 15832, 16243, 16251, 16283, 16291, 16459, 17147, 17587, 17779, 17947, 18115, 18267, 18835, 18987, 19243, 19315, 19672, 20308, 20392, 22579, 22587, 22987, 24243, 24427, 25387, 25507, 25843, 25963, 26323, 26548, 27619, 28267, 29227, 29635, 29827, 30235, 30867, 31315, 33643, 33667, 34003, 34387, 35347, 41083, 43723, 44923, 46363, 47587, 47923, 49723, 53827, 77683, 85507, 647, 1039, 1103, 1279, 1447, 1471, 1811, 1979, 2411, 2671, 3491, 3539, 3847, 3923, 4211, 4783, 5387, 5507, 5531, 6563, 6659, 6703, 7043, 9587, 9931, 10867, 10883, 12203, 12739, 13099, 13187, 15307, 15451, 16267, 17203, 17851, 18379, 20323, 20443, 20899, 21019, 21163, 22171, 22531, 24043, 25147, 25579, 25939, 26251, 26947, 27283, 28843, 30187, 31147, 31267, 32467, 34843, 35107, 37003, 40627, 40867, 41203, 42667, 43003, 45427, 45523, 47947, 90787, 695, 759, 1191, 1316, 1351, 1407, 1615, 1704, 1736, 1743, 1988, 2168, 2184, 2219, 2372, 2408, 2479, 2660, 2696, 2820, 2824, 2852, 2856, 2915, 2964, 3059, 3064, 3127, 3128, 3444, 3540, 3560, 3604, 3620, 3720, 3864, 3876, 3891, 3899, 3912, 3940, 4063, 4292, 4308, 4503, 4564, 4580, 4595, 4632, 4692, 4715, 4744, 4808, 4872, 4920, 4936, 5016, 5124, 5172, 5219, 5235, 5236, 5252, 5284, 5320, 5348, 5379, 5432, 5448, 5555, 5588, 5620, 5691, 5699, 5747, 5748, 5768, 5828, 5928, 5963, 5979, 6004, 6008, 6024, 6072, 6083, 6132, 6180, 6216, 6251, 6295, 6340, 6411, 6531, 6555, 6699, 6888, 6904, 6916, 7048, 7108, 7188, 7320, 7332, 7348, 7419, 7512, 7531, 7563, 7620, 7764, 7779, 7928, 7960, 7972, 8088, 8115, 8148, 8211, 8260, 8328, 8344, 8392, 8499, 8603, 8628, 8740, 8760, 8763, 8772, 8979, 9028, 9048, 9083, 9112, 9220, 9259, 9268, 9347, 9352, 9379, 9384, 9395, 9451, 9480, 9492, 9652, 9672, 9715, 9723, 9823, 9915, 9928, 9940, 10011, 10059, 10068, 10120, 10180, 10187, 10212, 10248, 10283, 10355, 10360, 10372, 10392, 10452, 10488, 10516, 10612, 10632, 10699, 10740, 10756, 10788, 10792, 10840, 10852, 10923, 11019, 11032, 11139, 11176, 11208, 11211, 11235, 11267, 11307, 11603, 11620, 11627, 11656, 11667, 11748, 11752, 11811, 11812, 11908, 11928, 12072, 12083, 12243, 12292, 12376, 12408, 12435, 12507, 12552, 12628, 12760, 12808, 12820, 12891, 13035, 13060, 13080, 13252, 13348, 13395, 13427, 13444, 13512, 13531, 13539, 13540, 13587, 13611, 13668, 13699, 13732, 13780, 13912, 14035, 14043, 14212, 14235, 14260, 14392, 14523, 14532, 14536, 14539, 14555, 14595, 14611, 14632, 14835, 14907, 14952, 14968, 14980, 15019, 15112, 15267, 15339, 15411, 15460, 15483, 15528, 15555, 15595, 15640, 15652, 15747, 15748, 15828, 15843, 15931, 15940, 15988, 16107, 16132, 16315, 16360, 16468, 16563, 16795, 16827, 16872, 16888, 16907, 16948, 17032, 17043, 17059, 17092, 17283, 17560, 17572, 17620, 17668, 17752, 17812, 17843, 18040, 18052, 18088, 18132, 18148, 18340, 18507, 18568, 18579, 18595, 18627, 18628, 18667, 18763, 18795, 18811, 18867, 18868, 18915, 19203, 19528, 19579, 19587, 19627, 19768, 19803, 19912, 19915, 20260, 20307, 20355, 20427, 20491, 20659, 20692, 20728, 20803, 20932, 20955, 20980, 20995, 21112, 21172, 21352, 21443, 21448, 21603, 21747, 21963, 21988, 22072, 22107, 22180, 22323, 22339, 22803, 22852, 22867, 22939, 23032, 23035, 23107, 23115, 23188, 23235, 23307, 23368, 23752, 23907, 23995, 24115, 24123, 24292, 24315, 24388, 24595, 24627, 24628, 24643, 24915, 24952, 24955, 25048, 25195, 25347, 25467, 25683, 25707, 25732, 25755, 25795, 25915, 25923, 25972, 25987, 26035, 26187, 26395, 26427, 26467, 26643, 26728, 26995, 27115, 27163, 27267, 27435, 27448, 27523, 27643, 27652, 27907, 28243, 28315, 28347, 28372, 28459, 28747, 28891, 29128, 29283, 29323, 29395, 29563, 29659, 29668, 29755, 29923, 30088, 30163, 30363, 30387, 30523, 30667, 30739, 30907, 30955, 30979, 31252, 31348, 31579, 31683, 31795, 31915, 32008, 32043, 32155, 32547, 32635, 32883, 33067, 33187, 33883, 34203, 34363, 34827, 34923, 36003, 36043, 36547, 36723, 36763, 36883, 37227, 37555, 37563, 38227, 38443, 38467, 39603, 39643, 39787, 40147, 40195, 40747, 41035, 41563, 42067, 42163, 42267, 42387, 42427, 42835, 43483, 44947, 45115, 45787, 46195, 46243, 46267, 47203, 47443, 47707, 48547, 49107, 49267, 49387, 49987, 50395, 52123, 52915, 54307, 55867, 56947, 57523, 60523, 60883, 61147, 62155, 62203, 63043, 64267, 79363, 84043, 84547, 111763, 479, 599, 1367, 2887, 3851, 4787, 5023, 5503, 5843, 7187, 7283, 7307, 7411, 8011, 8179, 9227, 9923, 10099, 11059, 11131, 11243, 11867, 12211, 12379, 12451, 12979, 14011, 14923, 15619, 17483, 18211, 19267, 19699, 19891, 20347, 21107, 21323, 21499, 21523, 21739, 21787, 21859, 24091, 24571, 25747, 26371, 27067, 27091, 28123, 28603, 28627, 28771, 29443, 30307, 30403, 30427, 30643, 32203, 32443, 32563, 32587, 33091, 34123, 34171, 34651, 34939, 36307, 37363, 37747, 37963, 38803, 39163, 44563, 45763, 48787, 49123, 50227, 51907, 54667, 55147, 57283, 57667, 57787, 59707, 61027, 62563, 63067, 64747, 66763, 68443, 69763, 80347, 85243, 89083, 93307]


# CLASS NUMBERS OF IMAGINARY QUADRATIC FIELDS
# http://www.ams.org/journals/mcom/2004-73-246/S0025-5718-03-01517-5/S0025-5718-03-01517-5.pdf
D_DB = [
    (1, 9, 163), (21, 85, 61483), (41, 109, 296587), (61, 132, 606643), (81, 228, 1030723),
    (2, 18, 427), (22, 139, 85507), (42, 339, 280267), (62, 323, 647707), (82, 402, 1446547),
    (3, 16, 907), (23, 68, 90787), (43, 106, 300787), (63, 216, 991027), (83, 150, 1074907),
    (4, 54, 1555), (24, 511, 111763), (44, 691, 319867), (64, 1672, 693067), (84, 1715, 1225387),
    (5, 25, 2683), (25, 95, 93307), (45, 154, 308323), (65, 164, 703123), (85, 221, 1285747),
    (6, 51, 3763), (26, 190, 103027), (46, 268, 462883), (66, 530, 958483), (86, 472, 1534723),
    (7, 31, 5923), (27, 93, 103387), (47, 107, 375523), (67, 120, 652723), (87, 222, 1261747),
    (8, 131, 6307), (28, 457, 126043), (48, 1365, 335203), (68, 976, 819163), (88, 1905, 1265587),
    (9, 34, 10627), (29, 83, 166147), (49, 132, 393187), (69, 209, 888427), (89, 192, 1429387),
    (10, 87, 13843), (30, 255, 134467), (50, 345, 389467), (70, 560, 811507), (90, 801, 1548523),
    (11, 41, 15667), (31, 73, 133387), (51, 159, 546067), (71, 150, 909547), (91, 214, 1391083),
    (12, 206, 17803), (32, 708, 164803), (52, 770, 439147), (72, 1930, 947923), (92, 1248, 1452067),
    (13, 37, 20563), (33, 101, 222643), (53, 114, 425107), (73, 119, 886867), (93, 262, 1475203),
    (14, 95, 30067), (34, 219, 189883), (54, 427, 532123), (74, 407, 951043), (94, 509, 1587763),
    (15, 68, 34483), (35, 103, 210907), (55, 163, 452083), (75, 237, 916507), (95, 241, 1659067),
    (16, 322, 31243), (36, 668, 217627), (56, 1205, 494323), (76, 1075, 1086187), (96, 3283, 1684027),
    (17, 45, 37123), (37, 85, 158923), (57, 179, 615883), (77, 216, 1242763), (97, 185, 1842523),
    (18, 150, 48427), (38, 237, 289963), (58, 291, 586987), (78, 561, 1004347), (98, 580, 2383747),
    (19, 47, 38707), (39, 115, 253507), (59, 128, 474307), (79, 175, 1333963), (99, 289, 1480627),
    (20, 350, 58507), (40, 912, 260947), (60, 1302, 662803), (80, 2277, 1165483), (100, 1736, 1856563),
]


def testPrime(p, limit=1<<35):
    semifactorization = (4*p-1).factor(limit=limit)
    minNonsquareBits = 0
    for (r, e) in semifactorization[:-1]:
        if e % 2 != 0:
            minNonsquareBits = minNonsquareBits + r.nbits()
    #if (minNonsquareBits) > 50, prime is probably not backdoored
    return (minNonsquareBits, semifactorization) #save these somewhere


class AutoJSONEncoder(json.JSONEncoder):
    """
    JSON encoder trying to_json() first
    """
    def default(self, obj):
        try:
            return obj.to_json()
        except AttributeError:
            return self.default_classic(obj)

    def default_classic(self, o):
        if isinstance(o, set):
            return list(o)
        elif isinstance(o, Integer):
            return int(o)
        elif isinstance(o, sage.rings.finite_rings.integer_mod.IntegerMod_abstract):
            return int(o)
        elif isinstance(o, bytes):
            return o.decode('utf8')
        else:
            try:
                return super(AutoJSONEncoder, self).default(o)
            except:
                return str(o)


def json_dumps(obj, **kwargs):
    """
    Json dump with the encoder
    :param obj:
    :param kwargs:
    :return:
    """
    return json.dumps(obj, cls=AutoJSONEncoder, **kwargs)


def gord(x, gen):
    """
    Return order of generator g in the mod group X
    :param x:
    :return:
    """
    return Zmod(x)(gen).multiplicative_order()


def order_of_generator(generator, m):
    totient = nt.totient(m)
    totient_decomposition = nt.factorint(totient)
    return element_order(generator, m, totient, totient_decomposition)


def element_order(element, modulus, order, order_decomposition):
    if element == 1:
        return 1  # by definition
    if pow(element, order, modulus) != 1:
        return None  # not an element of the group
    for factor, power in order_decomposition.items():
        for p in range(1, power + 1):
            next_order = order // factor
            if pow(element, next_order, modulus) == 1:
                order = next_order
            else:
                break
    return order


def bitsize(n):
    """
    Simple bitsize of n
    :param n:
    :return:
    """
    if n is None or int(n) == 0:
        return -1
    try:
        return math.log(int(n), 2)
    except ValueError:
        return -1


def try_get_cpu_info():
    """
    Returns CPU info
    https://github.com/workhorsy/py-cpuinfo
    :return:
    """
    try:
        import cpuinfo
        info = cpuinfo.get_cpu_info()
        if info is None:
            return None
        if 'flags' in info:
            del info['flags']
        return info

    except Exception as e:
        logger.error('Cpuinfo exception %s' % e)
        return None


def try_get_hostname():
    """
    Returns hostname or none
    :return:
    """
    try:
        import socket
        return socket.getfqdn()

    except Exception as e:
        logger.error('Hostname exception %s' % e)
        return None


def try_get_cpu_percent():
    """
    CPU usage before run
    :return:
    """
    try:
        import psutil
        return psutil.cpu_percent()
    except Exception as e:
        logger.error('Cpu percent exception %s' % e)
        return None


def try_get_cpu_load():
    """
    CPU unix-like load
    :return:
    """
    try:
        return os.getloadavg()
    except Exception as e:
        logger.error('Cpu load exception %s' % e)
        return None


def try_get_mem_used():
    try:
        import psutil
        process = psutil.Process(os.getpid())
        return process.memory_info().rss
    except Exception as e:
        logger.error('Mem usage exception %s' % e)
        return None


def try_get_max_mem_used():
    try:
        return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    except Exception as e:
        logger.error('Max mem usage exception %s' % e)
        return None


def record_worker(res):
    res['hostname'] = try_get_hostname()
    res['cpu_pcnt_load_after'] = try_get_cpu_percent()
    res['cpu_load_after'] = try_get_cpu_load()
    res['cpu'] = try_get_cpu_info()
    res['mem'] = try_get_mem_used()
    res['max_mem'] = try_get_max_mem_used()
    return res


def record_after(res):
    res['cpu_pcnt_load_after'] = try_get_cpu_percent()
    res['cpu_load_after'] = try_get_cpu_load()
    res['mem_after'] = try_get_mem_used()
    res['max_mem_after'] = try_get_max_mem_used()


def tsFactor(p, D):
    krn = kronecker(p, D)
    if krn == -1:
       return None
    if krn ==  1:
       K.<d> = QuadraticField(-D)
       return K.factor(4*p)[-1][0]


def is_undef(result):
    """
    Returns true if result returned from paralell processing is undefined / timeouted
    :param result:
    :return:
    """
    return result in UNDEF_RESULTS


@fork(timeout=10)
def reduced_generators(ideal):
    """
    Reduced generators computed in separate subprocess - faster
    :param ideal:
    :return:
    """
    return [list(x) for x in ideal.gens_reduced(proof=False)]


@fork(timeout=60*10)
def order_of_generator_timed(generator, m):
    return order_of_generator(generator, m)


def order_of_generator_compute(generator, m):
    """
    Computes order of generator.
    At first deterministically with timeout. If timeouts then estimate as (m-1)/2 + fermat test.
    :param generator:
    :param m:
    :return:
    """
    order = order_of_generator_timed(generator, m)
    if not is_undef(order):
        return order, 0

    order = int((m-1)/2)
    if pow(generator, order, m) == 1:
        return order, 1
    else:
        raise ValueError('Generator order unknown')


def top_n(n, generator):
    for _ in range(n): yield next(generator)


def detect_datafile(args):
    if args.mode == 1:
        suffix = ('_%s' % args.rand_type) if args.rand_type else ''
        return 'random' + suffix

    if args.data_file is not None:
        return args.data_file

    if args.data_dir is None:
        raise ValueError('Data dir not given')


    files = glob.glob(os.path.join(args.data_dir, '*.csv'))
    return files[args.data_file_idx]


def yield_usable_lines(fh):
    ctr = -1
    for idx, line in enumerate(fh):
        if line is None:
            continue

        line = line.strip()
        if len(line) == 0:
            continue

        if line.startswith('id') or 'id;' in line:
            continue

        ctr += 1
        yield (ctr, idx, line)


def factorfix(st):
    if st is None:
        return None
    if isinstance(st, list):
        return st
    p = [x.strip() for x in st.split('*')]
    res = []
    for cur in p:
        ex = [x.strip() for x in cur.split('^')]
        res.append((int(ex[0]), int(ex[1]) if len(ex)>1 else 1))
    return res


def normalize_card_name(name):
    name = name.replace(' - ', '_')
    name = name.replace('+', '')
    name = name.replace('-', '_')
    name = name.replace(' ', '_')
    name = name.lower()
    name = re.sub(r'[^a-zA-Z0-9_]', '', name)
    return name


def cluster_name(cn):
    if cn is None or len(cn) == 0:
        return ''
    prts = cn.split('.')
    nm = re.match(r'^([\w-]+?)([\d]+)$', prts[0])
    if nm is None:
        return cn
    return '%s.%s' % (nm.group(1), '.'.join(prts[1:]))


def unpack_keys(card_dir, out_dir, bitsize=512):
    files = glob.glob(os.path.join(card_dir, '*.rar'))
    filt = None if bitsize is None else ('%sb' % bitsize)
    if filt:
        files = [x for x in files if filt in x]
    logger.debug('Files: %s' % files)

    import tempfile
    from pyunpack import Archive

    for fl in files:
        dir_name = tempfile.mkdtemp(prefix='tmp_card', dir=out_dir)
        bname = os.path.basename(fl)
        bname = os.path.splitext(bname)[0]
        bname = normalize_card_name(bname)
        dest_file = os.path.join(out_dir, '%s.csv' % bname)
        fh = open(dest_file, 'w+')
        logger.debug('Processing %s to %s' % (bname, dest_file))

        try:
            Archive(fl).extractall(dir_name)
            csvs = glob.glob(os.path.join(dir_name, '*.csv'))
            for cl in csvs:
                logger.debug(' .. %s' % cl)

                with open(cl) as cfh:
                    data = cfh.read()
                fh.write(data)
                fh.flush()

        finally:
            shutil.rmtree(dir_name)
            fh.close()


def read_keys(args, data_file, basename='', num_keys=None, do_shuffle=True):
    if args.mode == 1:  # randomly generated keys, yield
        from sage.sets.primes import Primes
        pgens = Primes(False)

        if args.rand_prime is None:
            raise ValueError('In random mode specify rand-prime bit size')

        for i in range(num_keys):
            pq = []
            while len(pq) != 2:
                rstart = Integer(randrange(1 << args.rand_prime, (1<<(args.rand_prime + 1)) - 1))
                prime_cand = pgens.next(rstart)

                if args.rand_type is not None and args.rand_type == 1:
                    if (prime_cand - 1) % 3 == 0:
                        continue

                pq.append(prime_cand)

            cres = (i, i, i, pq[0], pq[1])
            yield cres
        return

    # Read chunk to process
    input_data = []
    num_keys_in_file = 0
    with open(data_file, 'r') as fh:
        gen = yield_usable_lines(fh)
        for _ in gen:
            num_keys_in_file += 1
    logger.debug('Number of usable keys %d in %s' % (num_keys_in_file, basename))

    # randomly generate sample with X keys, if applicable
    selection = set()
    while num_keys is not None and len(selection) < num_keys:
        r = randrange(0, num_keys_in_file - 1)
        if r in selection:
            continue
        selection.add(r)
    logger.debug('Keys selected: %s' % selection)
    logger.debug('Keys selected num: %s' % len(selection))

    # load the selection
    with open(data_file, 'r') as fh:
        gen = yield_usable_lines(fh)
        for ctr, idx, line in gen:
            if num_keys is not None and ctr not in selection:
                continue

            parts = line.split(';')
            kid = int(parts[0])
            p = int(parts[3], 16)
            q = int(parts[4], 16)
            cres = (ctr, idx, kid, p, q)
            input_data.append(cres)

    if do_shuffle:
        shuffle(input_data)
    for x in input_data:
        yield x


def recursive_dir_walk(folder):
    for dir_name, subs, fnames in os.walk(folder):
        for fname in fnames:
            yield os.path.join(dir_name, fname)


def yield_key_files(dirs):
    for folder in dirs:
        folder = os.path.abspath(folder)
        for x in recursive_dir_walk(folder):
            if not x.lower().endswith('.csv'):
                continue
            if os.path.isdir(x):
                continue
            cat = x[len(folder)+1:] if x.startswith(folder) else folder
            cat = os.path.dirname(cat)
            yield x, cat


def yield_4pm1_keys(data_dirs, keys_struct=None, fct=4):
    bitsizes_count = collections.defaultdict(lambda: 0) if keys_struct else None
    sub_files = yield_key_files(data_dirs)

    for fpath, cat in sub_files:
        with open(fpath, 'r') as fh:
            logger.debug('... srcfile: %s' % fpath)
            gen = yield_usable_lines(fh)
            for ctr, idx, line in gen:
                parts = line.split(';')
                kid = int(parts[0])
                p = int(parts[3], 16)
                q = int(parts[4], 16)

                if keys_struct:
                    cur_bit_size = int(get_round_bitsize(Integer(p)))
                    if keys_struct[cur_bit_size] <= bitsizes_count[cur_bit_size]:
                        break

                    bitsizes_count[cur_bit_size] += 2  # p, q; ahead, even if yields later

                yield (ctr, idx, kid, fct * p - 1, 0, cat)
                yield (ctr, idx, kid, fct * q - 1, 1, cat)


def yield_test_4pm1_keys(N=100):
    for i in range(N):
        yield (i, i, i, 4 * (generateCMprime(2*8+3, 512, False)) - 1, 0, '')
        yield (i, i, i, 4 * (generateCMprime(7*8+3, 512, False)) - 1, 0, '')
        yield (i, i, i, 4 * (rand_prime(512)) - 1, 0, '')
        yield (i, i, i, 4 * (generateCMprime(randrange(1, 1000) * 8 + 3, 512, False)) - 1, 0, '')


def yield_random_4pm1_keys(struct):
    idx = -1
    pgens = Primes(False)
    for rec in struct:
        bits = rec['bits']
        n = rec['n']
        tp = rec['type'] if 'type' in rec else None

        if tp == 'cm':
            d = rec['d']
            cat = 'rand_cm_%sb_%sd' % (bits, d)
            for i in range(n):
                idx += 1
                yield (idx, idx, i, 4 * (generateCMprime(d, 512, False)) - 1, 0, cat)

        elif tp == 'roca':
            raise ValueError('Not implemented yet')

        else:  # rand prime
            cat = 'rand_%sb' % bits
            for i in range(n):
                idx += 1
                yield (idx, idx, i, 4 * (rand_prime(bits, pgens)) - 1, 0, cat)


def producttree(X):
    result = [X]
    while len(X) > 1:
        X = [prod(X[i*2:(i+1)*2]) for i in range((len(X)+1)/2)]
        result.append(X)
    return result


def producttree_yield(X):
    yield [X]
    while len(X) > 1:
        X = [prod(X[i*2:(i+1)*2]) for i in range((len(X)+1)/2)]
        yield X


def remaindersusingproducttree(n,T):
    result = [n]
    for t in reversed(T):
        result = [result[floor(i/2)] % t[i] for i in range(len(t))]
    return result


def remainders(n,X):
   return remaindersusingproducttree(n,producttree(X))


def batchgcd_faster(X):
   prods = producttree(X)
   R = prods.pop()
   while prods:
        X = prods.pop()
        R = [R[floor(i/2)] % X[i]**2 for i in range(len(X))]
   return [gcd(r/n,n) for r,n in zip(R,X)]


def batchgcd_faster_yield(X):
    prods = producttree(X)
    R = prods.pop()
    while prods:
        X = prods.pop()
        R = [R[floor(i / 2)] % X[i] ** 2 for i in range(len(X))]

    prods = None  # memory clean
    for i in range(len(R)):
        r, n = R[i], X[i]
        yield gcd(r / n, n)


def yield_factor_possible(fcts, all_combs=False):
    if all_combs:
        exponents = [range(x[1]+1) for x in fcts]
        for cmb in itertools.product(*exponents):
            r = 1
            for i, ex in enumerate(cmb):
                r *= fcts[i][0]**ex
            yield r

    else:
        for fp in fcts:
            for ex in range(1, fp[1]+1):
                yield fp[0]**ex


def xgcd(f, g, N=1):
    toswap = False
    if f.degree() < g.degree():
        toswap = True
        f, g = g, f
    r_i = f
    r_i_plus = g
    r_i_plus_plus = f

    s_i, s_i_plus = 1, 0
    t_i, t_i_plus = 0, 1

    while (True):
        lc = r_i.lc().lift()
        lc *= r_i_plus.lc().lift()
        lc *= r_i_plus_plus.lc().lift()
        divisor = gcd(lc, N)
        if divisor > 1:
            return divisor, None, None

        q = r_i // r_i_plus
        s_i_plus_plus = s_i - q * s_i_plus
        t_i_plus_plus = t_i - q * t_i_plus
        r_i_plus_plus = r_i - q * r_i_plus
        if r_i_plus.degree() <= r_i_plus_plus.degree() or r_i_plus_plus.degree() == -1:
            if toswap == True:
                assert (r_i_plus == s_i_plus * f + t_i_plus * g)
                return r_i_plus, t_i_plus, s_i_plus
            else:
                assert (r_i_plus == s_i_plus * f + t_i_plus * g)
                return r_i_plus, s_i_plus, t_i_plus,
        r_i, r_i_plus = r_i_plus, r_i_plus_plus
        s_i, s_i_plus = s_i_plus, s_i_plus_plus
        t_i, t_i_plus = t_i_plus, t_i_plus_plus
        check_res = r_i == s_i * f + t_i * g
        if not check_res:
            logger.error('Assertion error: %s, %s != %s * %s + %s * %s' % (check_res, r_i, s_i, f, t_i, g))
            raise ValueError('xgcd assertion error')


def rand_prime(bits, pgens=None):
    pgens = Primes(False) if pgens is None else pgens
    rstart = Integer(randrange(1 << (bits-1), (1 << (bits)) - 1))
    return pgens.next(rstart)


def yield_rand_bitsize(ibits, rstop=None):
    rstart = 2^(ibits-1)
    rstop = 2*rstart - 1 if rstop is None else rstop
    offset = randrange(rstart, rstop)
    ctr = rstop - rstart
    while ctr > 0:
        yield offset
        offset = offset + 1
        if offset > rstop:  # overflow the top bound
            offset = rstart
        ctr -= 1


def isqrt2(n):
    # https://stackoverflow.com/questions/15390807/integer-square-root-in-python
    # int(sqrt()) has memory-leak
    # Sage has isqrt() which seems to work nice
    n = int(n)
    if n > 0r:
        x = 1r << (n.bit_length() + 1r >> 1r)
        while True:
            y = (x + n // x) >> 1r
            if y >= x:
                return int(x)
            x = y
    elif n == 0r:
        return 0r
    else:
        raise ValueError("square root not defined for negative numbers")


def generateCMprime_old(D, bits, verb = 1):
    if D % 8 != 3:
        raise ValueError('D must be congruent to 3 modulo 8')
    if verb == 1:
        logger.debug('Generating a suitable prime...')

    p = None
    ibits = int(floor(bits / 2 - log(D, 2) / 2 + 2))

    for i in yield_rand_bitsize(ibits, int(2^(ibits - 0.5))):  # randomized
        if i & 1 == 1:
            p = ZZ((D*i^2 + 1) / 4)
            if is_prime(p):
                return int(p)
    return None


def generateCMprime(D, bits, verb = 1):
    if D % 8 != 3:
        raise ValueError('D must be congruent to 3 modulo 8')

    p = None
    thresh_l = 1 << (bits - 1)
    thresh_h = (1 << bits) - 1

    # Exact bounds to cover the whole interval
    rstart = int(isqrt((4r*thresh_l-1r)/D))
    rstop  = int(isqrt((4r*thresh_h-1r)/D))+1r

    while True:
        p = random_cm_prime_sub(thresh_l, thresh_h, rstart, rstop, D)
        if p:
            return p


def yield_rand_primes(bits, pgens=None):
    pgens = Primes(False) if pgens is None else pgens
    thresh_l = int( 1r << (bits - 1r))
    thresh_h = int((1r << bits) - 1r)
    while True:
        i = ZZ(randrange(thresh_l, thresh_h))
        p = pgens.next(i)
        if p <= thresh_h and p >= thresh_l:
            yield p


def random_cm_prime_sub(thresh_l, thresh_h, rstart, rstop, D):
    while True:
        s = -1

        # Better is sqrt distribution as with uniform on i we get skew on i^2
        while True:
            s = randrange(thresh_l, thresh_h)
            s = int(isqrt((4r * s - 1r) / D))  # memory leak: s = int(sqrt((4 * s - 1) / D))
            if s & 1r == 1r and s >= rstart and s <= rstop:
                break

        p = int((D * s * s + 1r) / 4r)
        if p > thresh_h or p < thresh_l:
            continue
        if is_prime(p):
            return p


def yield_cm_primes(D, bits):
    if D % 8r != 3r:
        raise ValueError('D must be congruent to 3 modulo 8')

    p = None
    thresh_l = int( 1r << (bits - 1r))
    thresh_h = int((1r << bits) - 1r)

    # Exact bounds to cover the whole interval
    rstart = int(isqrt((4r * thresh_l - 1r) / D))
    rstop  = int(isqrt((4r * thresh_h - 1r) / D) + 1r)

    while True:
        p = random_cm_prime_sub(thresh_l, thresh_h, rstart, rstop, D)
        if p:
            yield p


def Qinverse(Q, a, N):
    """
    Q is a quotient ring of Z_N[x], a is the element to be inverted
    :param Q:
    :param a:
    :return:
    """
    j = Q.gens()[0]
    deg =  j.charpoly('X').degree()
    A = Q(a).matrix()
    det_a = det(A)
    logger.debug('DetA: %s' % det_a)

    factor = gcd(int(det_a), N)
    if factor!=1:  # a is not invertible
        raise ZeroDivisionError(a)

    else:
        Y = vector([1] + (deg-1)*[0])
        X = A.solve_left(Y)
        jvec = vector([j^i for i in [0..deg-1]])
        Xj = jvec*X
        return Xj


def Qinverse2 (Hx, a, time_res):
    ts = time.time()
    r,s,t = xgcd(a.lift(), Hx)
    txgcd = time.time()
    rinv = r[0]^(-1)
    res = s * rinv
    tres = time.time()

    time_res.time_qinv_char_poly = 0
    time_res.time_qinv_xgcd = txgcd - ts
    time_res.time_qinv_res = tres - txgcd
    return res


class AlgException(Exception):
    pass


class NotInvertibleException(AlgException):
    pass


class NotFactoredException(AlgException):
    pass


class FactorRes(object):
    def __init__(self, r=None, c=None, u=None, a=None, th=None, tq=None):
        self.r = r
        self.c = c
        self.u = u
        self.a = a
        self.time_hilbert = th
        self.time_q = tq
        self.time_a = None
        self.time_last_div = None
        self.time_last_gcd = None
        self.time_last_nrm = None
        self.time_total = 0
        self.time_agg_div = 0
        self.time_agg_gcd = 0
        self.time_agg_nrm = 0
        self.time_qinv_char_poly = 0
        self.time_qinv_xgcd = 0
        self.time_qinv_res = 0
        self.rand_elem = None
        self.fact_timeout = None
        self.out_of_time = False
        self.use_quinv2 = False
        self.use_cheng = False


def CMfactor(D, N, verb = 1, ctries=10, utries=10, fact_time=None, use_quinv2=False, use_cheng=False):
    """
    Try to factor N with respect to D, with ctries values of c and utries values of u
    """
    ts = time.time()
    Hx = hilbert_class_polynomial(-D)
    tth = time.time()
    if verb == 1:
        logger.debug('Hilbert polynomial computed for -%s!' % D)

    res = FactorRes()
    res.use_quinv2 = use_quinv2
    res.use_cheng = use_cheng

    ZN = Integers(N)
    R.<x> = PolynomialRing(ZN)

    ttq = time.time()
    if verb == 1:
        logger.debug('Q constructed!')

    try:
        if use_quinv2:
            Hx = R(Hx)
            Q.<j> = QuotientRing(R, R.ideal(Hx))
            a = Q(j * Qinverse2(Hx, 1728 - j, res))

        else:
            Q.<j> = ZN.extension(Hx)
            a = j * Qinverse(Q, 1728 - j, N)

    except ZeroDivisionError as noninv:
        logger.warning("is not invertible in Q! %s" % noninv)
        raise NotInvertibleException()

    if verb == 1:
        logger.debug('a computed')

    tta = time.time()
    res.time_agg_div = 0
    res.time_agg_gcd = 0
    res.time_hilbert = tth - ts
    res.time_q = ttq - tth
    res.time_a = tta - ttq
    res.a = None

    core_fnc = CMfactor_core
    if fact_time:
        time_left = fact_time - (tta - ts)
        logger.debug('Factorization timeout: %s' % time_left)
        res.fact_timeout = time_left
        core_fnc = fork(CMfactor_core, time_left)

    cres = core_fnc(N, ctries, utries, a, Q, ZN, Hx, res, use_cheng=use_cheng)
    if is_undef(cres):
        res.out_of_time = True
    else:
        res = cres

    tdone = time.time()
    res.time_total = tdone - ts
    return res


def CMfactor_core(N, ctries, utries, a, Q, ZN, Hx, res, use_cheng=False):
    is_done = False

    # We prove this takes only one iteration
    for c in [1..ctries]:
        E = EllipticCurve(Q, [0, 0, 0, 3 * a * c ^ 2, 2 * a * c ^ 3])
        logger.debug('EC ready')

        # expected number of u iterations: cn^2 / (cn^2 - 1)
        for u in [1..utries]:

            # Division polynomial is the most expensive part here
            tcs = time.time()
            rand_elem = ZN.random_element()
            res.rand_elem = int(rand_elem)

            w = E.division_polynomial(N, Q(rand_elem), two_torsion_multiplicity=0)
            ttdiv = time.time()
            logger.debug('Division polynomial done')

            if use_cheng:
                poly_gcd = xgcd(w.lift(), Hx, N)[0]
                ttnrm = time.time()
                r = gcd(ZZ(poly_gcd), N)
                ttgcd = time.time()

            else:
                nrm = w.norm()
                ttnrm = time.time()
                r = gcd(nrm, N)
                ttgcd = time.time()

            res.time_agg_div += ttdiv - tcs
            res.time_agg_gcd += ttgcd - ttdiv
            res.time_agg_nrm += ttnrm - ttdiv
            res.c = int(c)
            res.u = int(u)
            res.time_last_div = ttdiv - tcs
            res.time_last_gcd = ttgcd - ttdiv
            res.time_last_nrm = ttnrm - ttdiv

            if r > 1:
                res.r = int(r)
                logger.debug('A factor of N: %s' % r)
                logger.debug('c: %s, u: %s' % (c, u))
                is_done = True
                break

            else:
                logger.info('u failed: %s, next_attempt' % u)

        if is_done:
            break

    return res


def class_number(d):
    k = QuadraticField(-d, 'x')
    return k.class_number()


def is_res_ok(fpath):
    if not os.path.exists(fpath):
        return False
    try:
        with open(fpath) as fh:
            js = json.load(fh)
            if js is None or 'results' not in js:
                return False
            if js['results'] is None:
                return False
            return True
    except:
        return False


def avg_(it):
    return sum(it) / float(len(it))


def should_terminate_job(args, time_start):
    if args.job_time is None or args.job_time <= 0:
        return False

    ct = time.time()
    return (ct - time_start) >= args.job_time


def get_round_bitsize(p):
    bsize = p.nbits()
    if bsize < 90:
        return bsize
    elif bsize >= 90 and bsize < 134:
        return 128
    elif bsize >= 247 and bsize < 265:
        return 256
    elif bsize >= 490 and bsize < 522:
        return 512
    elif bsize >= 1000 and bsize < 1044:
        return 1024
    elif bsize >= 2020 and bsize < 2077:
        return 2048
    else:
        return bsize


def timed_class_number(d, timeout):
    if d < (1<<34):
        return class_number(d)
    else:
        return fork(class_number, timeout=timeout)(d)


def bin_bits(n):
    return int(n).bit_length()


def keys_struct_parse(keys_struct):
    res = collections.defaultdict(lambda: 0)
    for x in keys_struct:
        res[x['bits']] = x['n']
        if 'type' in x:
            raise ValueError('Different types not supported')
    return res


def class_poly(class_poly, disc, modulus=0):
    p = subprocess.Popen("%s -%s 0 %s -" % (class_poly, disc, modulus),
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)

    output, err = p.communicate()
    p_status = p.wait()
    if p_status != 0:
        logger.warning('Error from classpoly. Code: %s, err: %s' % (p_status, err))
        return None, None

    return len(output), err


def work_sample(args):
    """
    Sample D, compute class number
    :param args:
    :return:
    """
    fnc_class_number = timed_class_number
    sys.setrecursionlimit(50000)
    pari.allocatemem(3561823232)  # pari stack size, for class num

    time_start = time.time()
    js = collections.OrderedDict()
    js['time_start'] = time_start
    js['timeout'] = args.timeout
    js['limit'] = args.limit
    js['batch_idx'] = args.batch_idx
    js['job_time'] = args.job_time
    js['exp'] = args.exp
    js['expired_time'] = False
    js['known_d'] = args.known_d
    js['needed_d'] = args.needed_d
    js['needed_d_offset'] = args.needed_d_offset
    js['needed_d_len'] = args.needed_d_len

    exp_suffix = '' if args.exp == '0' else ('_%s' % args.exp)
    res_file = os.path.join(args.res_dir, 'sample_d%s_%04d.json' % (exp_suffix, args.batch_idx,))
    res_file_stream = os.path.join(args.res_dir, 'res_sample_d%s_%04d.json' % (exp_suffix, args.batch_idx,))
    res_file_stream_fh = open(res_file_stream, 'w+')

    time_start_logic = time_start - 17 * 60  # init time before control flow reached + finalization
    logger.info('Res file: %s' % res_file)
    logger.info('Res file stream: %s' % res_file_stream)

    last_flush = time.time()
    last_times = []
    last_time = time.time()
    timed_out = []
    known_d = None if args.known_d is None else set(json.load(open(args.known_d)))
    needed_d = None if args.known_d is None else json.load(open(args.needed_d))

    compute_chunk = True if needed_d else False
    needed_d_chunk = needed_d[args.needed_d_offset:] if needed_d else None
    if needed_d_chunk:
        logger.info('Needed D: %s; offset: %s' % (args.needed_d, args.needed_d_offset))
    if needed_d and args.needed_d_len:
        logger.info('Needed-D Length: %s' % args.needed_d_len)
        needed_d_chunk = needed_d_chunk[:args.needed_d_len]

    # process input data
    res = []
    computed = 0
    while True:
        is_sf = False

        # Various relations strategies
        if compute_chunk:
            is_sf =  True
            # Computing needed D-CN relations
            if len(needed_d_chunk) == 0:
                break
            d_cand = needed_d_chunk.pop()
            if known_d and d_cand in known_d:
                continue
        else:
            # Compute D-CN relations by random sampling
            if computed >= args.num:
                break

            d_cand = randrange(11, args.limit)
            if d_cand % 8 != 3:
                continue

            if known_d and d_cand in known_d:
                continue

            is_sf = Integer(d_cand).is_squarefree()
            if not is_sf:
                continue

        logger.debug('Processing d: %s' % d_cand)
        t_start = time.time()
        dres = fnc_class_number(d_cand, args.timeout)
        dres = None if is_undef(dres) else dres
        res_time = time.time() - t_start

        if dres:
            cres = collections.OrderedDict()
            cres['d'] = d_cand
            cres['k'] = dres
            cres['sf'] = is_sf
            cres['time'] = res_time

            res_file_stream_fh.write(json_dumps(cres) + '\n')
            res.append(cres)

        else:
            timed_out.append(d_cand)

        computed += 1
        if (time.time() - last_flush) > 100:
            res_file_stream_fh.flush()
            last_flush = time.time()

        ctime = time.time()
        last_times.append(ctime - last_time)
        last_time = ctime

        last_times = last_times[-100:]
        avg_time = sum(last_times) / len(last_times)

        if should_terminate_job(args, time_start_logic - avg_time):
            logger.info('Running out of time...')
            js['expired_time'] = True
            break

    res_file_stream_fh.close()

    js['num_computed'] = computed
    js['time_total'] = time.time() - time_start
    js['timed_out'] = timed_out
    js['results'] = res
    record_after(js)

    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))

    logger.info('Job done')


def work_factor(args):
    disc = args.disc
    class_num = class_number(disc)
    tstime = time.time()
    sys.setrecursionlimit(50000)  # for the computation of division polynomials

    file_exp = args.file_exp if args.file_exp is not None else args.exp
    exp_suffix = '' if file_exp == '0' else ('_%s' % file_exp)
    res_file = os.path.join(args.res_dir, 'factor%s_k%05d_d%014d_b%04d_%04d.json' % (exp_suffix, class_num, disc, args.prime_bits, args.batch_idx))
    ts = time.time()
    logger.debug('Res file: %s' % res_file)
    logger.debug('D: %s, class_num: %s' % (disc, class_num))

    if not args.force and is_res_ok(res_file):
        logger.info('Result file already generated: %s' % res_file)
        return

    js = collections.OrderedDict()
    js['time_start'] = ts
    js['disc'] = disc
    js['class_num'] = class_num
    js['prime_bits'] = args.prime_bits
    js['batch_idx'] = args.batch_idx
    js['job_time'] = args.job_time
    js['exp'] = args.exp

    res = None
    try:
        p = generateCMprime(disc, args.prime_bits)
        tp = time.time()
        js['time_prime'] = tp - ts
        js['p'] = int(p)

        q = rand_prime(args.prime_bits)
        N = p * q
        js['q'] = int(q)
        js['N'] = int(N)
        logger.debug('p: %s' % p)
        logger.debug('N: %s' % N)

        tf_start = time.time()
        factor_timeout = args.job_time - 10 * 60 - (tf_start - tstime) if args.job_time else None
        res = CMfactor(disc, N, 1, fact_time=factor_timeout, use_quinv2=args.qinv2, use_cheng=args.cheng)
        res = -1 if is_undef(res) else res
        tf = time.time()

        js['time_factor'] = tf - tf_start
        js['results'] = res.__dict__ if res and not isinstance(res, int) else None

    except Exception as e:
        logger.warning('Exception: %s' % e)
        traceback.print_exc()

        js['error'] = str(e)
        js['results'] = None

    tdone = time.time()
    js['time_total'] = tdone - ts
    logger.debug('Time total: %s' % js['time_total'])

    record_worker(js)

    if args.force and is_res_ok(res_file):
        res_new = '%s.%s_expired' % (res_file, time.time())
        logger.info('Result file already generated: %s, moving to: %s' % (res_file, res_new))
        try:
            os.rename(res_file, res_new)
        except Exception as e:
            logger.error('Exception in moving: %s' % e)

    record_after(js)
    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))


def work(args):
    """
    Main entry routine.
    Testing particular key file (index in the lexicographic dir listing ordering or file name),

    Operation mode 1:
     - testing n primes (p,q from RSA key), depending on the input index and batch size. Prime selection
       is incremental.

    :param args:
    :return:
    """
    if args.unpack:
        unpack_keys(args.data_dir, out_dir=args.res_dir, bitsize=int(args.unpack))
        return

    if args.max_keys and args.job_time is None:
        raise ValueError('Job time has to be specified for max keys')

    time_start = time.time()
    js = collections.OrderedDict()
    js['mode'] = args.mode
    js['time_start'] = time_start

    if args.mode not in [0, 1]:
        raise ValueError('Unknown mode')

    js['data_dir'] = args.data_dir
    js['data_file_idx'] = args.data_file_idx
    js['data_file'] = args.data_file

    data_file = detect_datafile(args)
    js['data_file_used'] = data_file

    limit = 1 << args.limit if args.limit > 0 else None
    js['timeout'] = args.timeout
    js['limit'] = args.limit

    num_keys = args.num_keys if args.num_keys is not None else ((2*60*60 - 600) // args.timeout // 2)  # 2 hours job, num of primes
    if args.max_keys:
        num_keys = 9999

    js['num_keys'] = num_keys
    js['batch_idx'] = args.batch_idx
    js['max_keys'] = args.max_keys
    js['job_time'] = args.job_time

    basename = os.path.basename(data_file)

    # load the selection
    input_data = read_keys(args, data_file, basename, 50000 if args.max_keys else num_keys)

    file_dec = str(args.file_dec)
    res_file = os.path.join(args.res_dir, ('semifactor_%s_%s_n%0' + file_dec + 'd_b%04d.json') % (args.exp, basename, num_keys, args.batch_idx))
    res_file_stream = os.path.join(args.res_dir, ('res_semifactor_%s_%s_n%0' + file_dec + 'd_b%04d.json') % (args.exp, basename, num_keys, args.batch_idx))
    res_file_stream_fh = open(res_file_stream, 'w+')

    # process input data
    res = []
    num_factored = 0
    num_keys_computed = 0
    fnc_test_prime = fork(testPrime, timeout=args.timeout)
    time_start_logic = time_start - 10 * 60  # init time before control flow reached + finalization

    for ctr, idx, kid, p, q in input_data:
        logger.debug('Processing key: %s, P' % ctr)
        p_res_start = time.time()
        p_res = fnc_test_prime(p, limit=limit)
        p_res_time = time.time() - p_res_start

        logger.debug('Processing key: %s, Q' % ctr)
        q_res_start = time.time()
        q_res = fnc_test_prime(q, limit=limit)
        q_res_time = time.time() - q_res_start

        p_res = None if is_undef(p_res) else (p_res[0], list(p_res[1]))
        q_res = None if is_undef(q_res) else (q_res[0], list(q_res[1]))

        cres = collections.OrderedDict()
        cres['ctr'] = ctr
        cres['idx'] = idx
        cres['kid'] = kid
        cres['p'] = hex(p)
        cres['q'] = hex(q)
        cres['p_res'] = p_res  # minNonsquareBits, semifactorization
        cres['p_res_time'] = p_res_time
        cres['q_res'] = q_res  # minNonsquareBits, semifactorization
        cres['q_res_time'] = q_res_time

        if p_res is not None:
            num_factored += 1
        if q_res is not None:
            num_factored += 1
        num_keys_computed += 1

        res_file_stream_fh.write(json_dumps(cres) + '\n')
        res_file_stream_fh.flush()

        res.append(cres)

        # terminating if maxkeys
        if args.max_keys:
            time_left = args.job_time - (time.time() - time_start_logic)
            if time_left < 2 * args.timeout:
                break

    res_file_stream_fh.close()

    js['num_keys_computed'] = num_keys_computed
    js['num_factored'] = num_factored
    js['time_total'] = time.time() - time_start
    js['results'] = res
    record_after(js)

    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))


def test_hilberts():
    hilbert_samples = [3, 11, 19, 35, 43, 51, 59, 67, 83, 91, 107, 115, 123, 131] + [2 ** x + 3 for x in range(8, 23)]
    hilbert_avg = collections.defaultdict(lambda: [])
    for smpl in hilbert_samples:
        for att in range(5):
            ts = time.time()
            Hx = hilbert_class_polynomial(-smpl)
            tth = time.time()
            hilbert_avg[smpl].append(tth-ts)
        print('Hilbert: %8d: %s' % (smpl, avg_(hilbert_avg[smpl])))


def work_batch_gcd(args):
    time_start = time.time()
    js = collections.OrderedDict()
    data_dirs = [x for x in ([args.data_dir] + args.data_dirs) if x]
    js['mode'] = args.mode
    js['action'] = 'bgcd'
    js['time_start'] = time_start
    js['data_dir'] = data_dirs
    limit = 1 << args.limit if args.limit > 0 else None
    js['timeout'] = args.timeout
    js['limit'] = args.limit
    js['pm1'] = args.pm1
    js['no_d_phase'] = args.no_d_phase
    js['bgcd_per_src'] = args.bgcd_per_src

    num_keys = args.num_keys if args.num_keys is not None else None
    if args.max_keys:
        num_keys = 9999

    random_keys_struct = json.loads(args.random_keys_struct) if args.random_keys_struct else None
    keys_struct = json.loads(args.keys_struct) if args.keys_struct else None

    if args.random_keys_struct_file:
        random_keys_struct = json.load(open(args.random_keys_struct_file))
    if args.keys_struct_file:
        keys_struct = json.load(open(args.keys_struct_file))
    if keys_struct:
        keys_struct = keys_struct_parse(keys_struct)

    js['num_keys'] = num_keys
    js['batch_idx'] = args.batch_idx
    js['max_keys'] = args.max_keys
    js['job_time'] = args.job_time
    js['all_combs'] = args.all_combs
    js['random_keys'] = args.random_keys
    js['prime_bits'] = args.prime_bits
    js['random_keys_struct'] = random_keys_struct
    js['timeout'] = False
    record_worker(js)
    logger.info('Job started')

    sufx = '_pf' if args.postfactor else ''
    file_dec = str(args.file_dec)
    res_file = os.path.join(args.res_dir, ('bgcd_%s_%s_n%0' + file_dec + 'd_b%04d%s.json') % (
    args.exp, 'all', num_keys if num_keys else 0, args.batch_idx, sufx))
    res_file_stream = os.path.join(args.res_dir, ('res_bgcdr_%s_%s_n%0' + file_dec + 'd_b%04d%s.json') % (
    args.exp, 'all', num_keys if num_keys else 0, args.batch_idx, sufx))
    res_file_stream_fh = open(res_file_stream, 'w+')

    computed_data = json.load(open(args.bgcd)) if args.bgcd else None  # already computed

    # process input data
    res = []
    num_keys_read = 0
    num_factored = 0
    num_keys_computed = 0
    fnc_factor = fork(factor, timeout=5 if not args.postfactor else 60)
    time_start_logic = time_start - 10 * 60 - 10 * 60  # init time before control flow reached + finalization

    # Read all primes, compute batch GCD
    all_keys = []
    key_data = []
    cats_reg = {}
    cats_reg_rev = {}
    cats_idx = {}
    cats_count = collections.defaultdict(lambda: 0)
    bitsizes_count = collections.defaultdict(lambda: 0)
    fnc_read_keys = yield_4pm1_keys(data_dirs, keys_struct, 1 if args.pm1 else 4)
    dump_key_idx = None if len(args.key_ids) == 0 else set(args.key_ids)
    logger.info(dump_key_idx)
    if args.test:
        fnc_read_keys = yield_test_4pm1_keys(10)
    if random_keys_struct:
        fnc_read_keys = yield_random_4pm1_keys(random_keys_struct)

    # Read keys, prepare data
    logger.info('Res file: %s' % res_file)
    logger.info('Reading keys from: %s' % data_dirs)
    for iidx, pkey_dat in enumerate(fnc_read_keys):
        ctr, idx, kid, fpm1, is_q, cat = pkey_dat
        if fpm1 <= 1:  # dataset without primes
            continue

        if iidx % 1000000 == 0:
            logger.debug('Keys read: %s, cat: %s' % (iidx, cat))

        cur_bit_size = int(get_round_bitsize(fpm1))
        if keys_struct and keys_struct[cur_bit_size] <= bitsizes_count[cur_bit_size]:
            continue  # structure of prime bit sizes - to match another experiment, ref vs. actual distrib.

        num_keys_read += 1
        if dump_key_idx and (num_keys_read-1) in dump_key_idx:
            logger.info('Requested key: %s, ctr: %s, idx=line: %s, kid: %s, fpm1: %s, is_q: %s, cat: %s'
                        % (num_keys_read-1, ctr, idx, kid, fpm1, is_q, cat))

        if num_keys is not None and num_keys_read > num_keys:
            break

        cat_id = None
        if cat in cats_reg:
            cat_id = cats_reg[cat]
        else:
            cat_id = len(cats_reg)
            cats_reg[cat] = cat_id
            cats_reg_rev[cat_id] = cat
            cats_idx[cat_id] = num_keys_read - 1
            logger.info('New key category: [%s]' % cat)

        cats_count[cat_id] += 1
        bitsizes_count[cur_bit_size] += 1
        if args.key_count_only:
            continue

        all_keys.append(fpm1)
        key_data.append((int(ctr), int(is_q), int(cat_id)))

    js['keys_struct'] = keys_struct
    js['cats_reg'] = cats_reg
    js['cats_reg_rev'] = cats_reg_rev
    js['cats_idx'] = cats_idx
    js['cats_count'] = cats_count
    js['bitsizes_count'] = bitsizes_count

    logger.info('Keys: %s' % num_keys_read)
    if args.key_count_only:
        logger.info(json_dumps(js, indent=2))
        return

    logger.info('Keys loaded, first 1 keys: %s' % (all_keys[:1] if len(all_keys) > 1 else '?'))
    logger.info('Computing batch GCD on %s keys ...' % len(all_keys))
    logger.info('Data: %s' % json_dumps(js))
    if args.bgcd_computed and computed_data:
        gcd_res = computed_data['gcd_res']
    elif args.bgcd_per_src:
        gcd_res = []
        for cat_id in range(len(cats_reg)):
            fin = cats_idx[cat_id+1] if (cat_id + 1) in cats_idx else None
            gcd_res += batchgcd_faster(all_keys[cats_idx[cat_id]:fin])
    else:
        gcd_res = batchgcd_faster(all_keys)

    logger.info('Checking discriminants ...')
    last_idx = None
    fact_err = []
    found_discs = []
    gcd_res_filt = []

    iter_gcds = enumerate(gcd_res)
    if args.postfactor:
        iter_gcds = [(int(x[0]), int(x[1])) for x in computed_data['fact_err']]
    if args.no_d_phase:
        iter_gcds = []

    # Compute Discriminants
    for idx, x in iter_gcds:
        if x == 1:
            continue

        if should_terminate_job(args, time_start_logic):
            logger.info('Running out of time...')
            js['timeout'] = True
            break

        bsize = Integer(x).nbits()
        if bsize > 90:
            logger.debug('Large GCD: %s for %s, bits: %s' % (x, idx, bsize))

        # factorize with timeout
        if args.postfactor:
            fcts = factor(x) if bsize <= 230 else fnc_factor(x)
        else:
            fcts = fnc_factor(x) if bsize >= 128 else factor(x)

        if is_undef(fcts):
            fact_err.append((idx, x, all_keys[idx]))
            logger.warning('Cannot factorize in time: %s, bsize: %s, idx: %s' % (x, bsize, idx))
            continue

        fcts = list(fcts)
        poss = yield_factor_possible(fcts, args.all_combs)
        for cand in poss:
            if cand % 8 != 3:
                continue
            # assert all_keys[idx] % cand == 0
            resid = all_keys[idx] // cand
            if is_square(resid):
                ckey_data = key_data[idx]
                cres = (int(idx), int(cand), ckey_data, int(all_keys[idx]))
                found_discs.append(cres)
                logger.info(' !! FOUND d: %s for idx: %s : %s, prime: %s' % (cand, idx, str(ckey_data), all_keys[idx]))

                res_file_stream_fh.write(json_dumps(cres) + '\n')
                res_file_stream_fh.flush()

        last_idx = idx

    res_file_stream_fh.close()
    logger.info('Finishing ...')
    # js['num_keys_computed'] = num_keys_computed
    # js['num_factored'] = num_factored
    js['last_idx'] = last_idx
    js['time_total'] = time.time() - time_start
    js['found_discs'] = found_discs
    js['fact_err'] = fact_err
    js['gcd_res'] = gcd_res  # quite bloaty

    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))

    logger.info('Job done')


# @memprof
#@profile
def work_gen_prime(args):
    time_start = time.time()
    js = collections.OrderedDict()
    js['mode'] = args.mode
    js['action'] = 'gen_prime'
    js['time_start'] = time_start
    js['timeout'] = args.timeout
    js['limit'] = args.limit
    js['disc'] = args.disc
    js['cm_primes'] = args.cm_primes

    #  256b, 2000x:   1.923
    #  512b, 2000x:  14.87
    # 1024b, 2000x: 161.195

    num_keys = args.num_keys if args.num_keys is not None else None
    if args.max_keys:
        num_keys = 0

    random_keys_struct = json.loads(args.random_keys_struct) if args.random_keys_struct else None
    if args.random_keys_struct_file:
        random_keys_struct = json.load(open(args.random_keys_struct_file))
    if random_keys_struct is None:
        random_keys_struct = [{'bits': args.prime_bits, 'n': num_keys}]
        if args.cm_primes:
            random_keys_struct[0]['type'] = 'cm'
            random_keys_struct[0]['d'] = args.disc

    prime_bits = random_keys_struct[0]['bits']
    num_keys = random_keys_struct[0]['n']

    key_tp = random_keys_struct[0]['type'] if 'type' in random_keys_struct[0] else None
    key_d = random_keys_struct[0]['d'] if key_tp and key_tp=='cm' else None

    js['num_keys'] = num_keys
    js['batch_idx'] = args.batch_idx
    js['job_time'] = args.job_time
    js['prime_bits'] = prime_bits
    js['random_keys_struct'] = random_keys_struct
    js['timeout'] = False
    record_worker(js)
    logger.info('Job started: %s' % json_dumps(js))
    logger.info('Keytp: %s, keyd: %s' % (key_tp, key_d))

    fname_base = 'moduli' if args.gen_moduli else 'primes'
    file_dec = str(args.file_dec)
    res_file = os.path.join(args.res_dir, ('%s_%s_%sb_n%0' + file_dec + 'd_b%04d.json') % (
        fname_base, args.exp, prime_bits, num_keys if num_keys else 0, args.batch_idx))
    res_file_stream = os.path.join(args.res_dir,  ('res_%s_%s_%sb_n%0' + file_dec + 'd_b%04d.csv') % (
        fname_base, args.exp, prime_bits, num_keys if num_keys else 0, args.batch_idx))
    res_file_stream_fh = open(res_file_stream, 'w+')

    # process input data
    time_start_logic = time_start - 15 * 60  # init time before control flow reached + finalization
    logger.info('res_file: %s' % res_file)
    logger.info('res_file_stream: %s' % res_file_stream)

    # Read all primes, compute batch GCD
    last_times = []
    last_time = time.time()
    num_primes = -1

    # Support multiple prime formats
    pgens = Primes(False)
    c_rand_prime = yield_rand_primes(prime_bits, pgens)
    c_rand_cm_prime = yield_cm_primes(key_d, prime_bits)
    local_rand_prime = c_rand_cm_prime if key_d else c_rand_prime

    for i in range(num_keys if num_keys else 10000000r):
        if should_terminate_job(args, time_start_logic):
            logger.info('Running out of time...')
            break

        if args.gen_moduli:
            prime_p = next(local_rand_prime)
            prime_q = next(c_rand_prime)  # second one is always normal prime
            modulus = prime_p * prime_q
            if bin_bits(modulus) != 2r*prime_bits:
                continue

            num_primes += 1  # id;n;e;p;q;d;t
            res_file_stream_fh.write('%s;%x;0;%x;%x;0;0\n' % (i, int(modulus), int(prime_p), int(prime_q)))

        else:
            num_primes += 1
            pr = next(local_rand_prime)
            res_file_stream_fh.write('%x\n' % pr)

        if num_primes % 100 == 0:
            res_file_stream_fh.flush()
            gc.collect()

        ctime = time.time()
        last_times.append(ctime - last_time)
        last_time = ctime

        last_times = last_times[-100:]
        prime_time = sum(last_times) / len(last_times)

        if should_terminate_job(args, time_start_logic - prime_time):
            logger.info('Running out of time...')
            break

    res_file_stream_fh.close()

    # from guppy import hpy
    # h = hpy()
    # print(h.heap())

    logger.info('Finishing ...')
    js['num_keys'] = num_primes
    js['time_total'] = time.time() - time_start
    record_after(js)

    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))

    logger.info('Job done, time: %s, mem: %s, max mem: %s' % (js['time_total'], try_get_mem_used(), try_get_max_mem_used()))


def work_primorial_d(args):
    sys.setrecursionlimit(50000)
    pari.allocatemem(3561823232)  # pari stack size, for class num

    time_start = time.time()
    js = collections.OrderedDict()
    js['time_start'] = time_start
    js['timeout'] = args.timeout
    js['limit'] = args.limit
    js['batch_idx'] = args.batch_idx
    js['job_time'] = args.job_time
    js['exp'] = args.exp
    js['num'] = args.num
    js['expired_time'] = False
    js['known_d'] = args.known_d

    exp_suffix = '' if args.exp == '0' else ('_%s' % args.exp)
    res_file = os.path.join(args.res_dir, 'primorial_d_d%s_%04d.json' % (exp_suffix, args.batch_idx,))
    res_file_stream = os.path.join(args.res_dir, 'res_primorial_d_d%s_%04d.csv' % (exp_suffix, args.batch_idx,))
    res_file_stream_fh = open(res_file_stream, 'w+')

    time_start_logic = time_start - 17 * 60  # init time before control flow reached + finalization
    logger.info('Res file: %s' % res_file)
    logger.info('Res file stream: %s' % res_file_stream)
    known_d = json.load(open(args.known_d))
    known_d_ln = len(known_d)
    batch_size = known_d_ln // args.num

    known_half = int(batch_size*(0.5+args.batch_idx))
    known_end = batch_size*(1+args.batch_idx) if args.num <= args.batch_idx + 1 else None

    known_d_fetch_l = known_d[batch_size*args.batch_idx : known_half]
    known_d_fetch_r = known_d[known_half : known_end]

    js['known_d_size'] = known_d_ln
    js['job_time'] = args.job_time
    js['interval_start'] = batch_size * args.batch_idx
    js['interval_stop'] = known_end
    js['interval_half'] = known_half

    js['timeout'] = False
    record_worker(js)
    logger.info('Job started: %s' % json_dumps(js))

    XX = product(known_d_fetch_l)
    logger.info('L computed, computing R ...')

    XY = product(known_d_fetch_r)

    res_file_stream_fh.write('%s;%x;0;%x;%x;0;0\n' % (0, 0, int(XX), int(XY)))
    res_file_stream_fh.close()

    logger.info('Finishing ...')
    js['time_total'] = time.time() - time_start

    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))

    logger.info('Job done')


def work_hilbert(args):
    time_start = time.time()
    js = collections.OrderedDict()
    js['time_start'] = time_start
    js['timeout'] = args.timeout
    js['limit'] = args.limit
    js['batch_idx'] = args.batch_idx
    js['job_time'] = args.job_time
    js['exp'] = args.exp
    js['expired_time'] = False
    js['job_time'] = args.job_time
    if len(args.cns) != len(args.discs):
        raise ValueError('Inconsistent arguments')
    
    classpoly = os.getenv('CLASSPOLY')
    js['classpoly'] = classpoly

    pgens = Primes(False)
    prim = pgens.next(1<<4096)

    exp_suffix = '' if args.exp == '0' else ('_%s' % args.exp)
    res_file = os.path.join(args.res_dir, 'hilb_d_d%s_%04d.json' % (exp_suffix, args.batch_idx,))
    res_file_stream = os.path.join(args.res_dir, 'res_hilb_d_d%s_%04d.csv' % (exp_suffix, args.batch_idx,))
    res_file_stream_fh = open(res_file_stream, 'w+')

    time_start_logic = time_start - 17 * 60  # init time before control flow reached + finalization
    logger.info('Res file: %s' % res_file)
    logger.info('Res file stream: %s' % res_file_stream)

    js['timeout'] = False
    record_worker(js)
    logger.info('Job started: %s' % json_dumps(js))

    res = []
    for idx in range(len(args.discs)):
        if should_terminate_job(args, time_start_logic):
            js['timeout'] = True
            logger.info('Running out of time...')
            break

        disc = args.discs[idx]
        cn = args.cns[idx]
        logger.info('Computing CN=%s, D=%s, idx=%s/%s' % (cn, disc, idx, len(args.discs)))

        ts = time.time()
        clen, err = class_poly(classpoly, disc, prim)
        if clen is None:
            continue

        logger.info('Computed in: %s' % (time.time() - ts))
        logger.debug('Err: %s' % err)

        cres = {'d':disc, 'k':cn, 'time': (time.time() - ts), 'len': clen}
        res.append(cres)

        res_file_stream_fh.write('%s\n' % json_dumps(cres))
        res_file_stream_fh.write('%s\n' % json_dumps({'err':err}))
        res_file_stream_fh.flush()

    res_file_stream_fh.close()

    logger.info('Finishing ...')
    js['time_total'] = time.time() - time_start
    js['res'] = res

    with open(res_file, 'w+') as fh:
        fh.write(json_dumps(js, indent=2))

    logger.info('Job done')


def main():
    parser = argparse.ArgumentParser(description='CM factorization script')
    parser.add_argument('--action', dest='action', action="store", default="test_prime",
                        help='Primary action')

    parser.add_argument('--mode', dest='mode', action="store", type=int, default=0,
                        help='Mode of operation')
    parser.add_argument('--exp', dest='exp', action="store", default='0',
                        help='Experiment setup')
    parser.add_argument('--file-exp', dest='file_exp', action="store", default=None,
                        help='Experiment result ID')

    parser.add_argument('--data-dir', dest='data_dir', action="store",
                        help='Directory with input data files')

    parser.add_argument('--data-dirs', dest='data_dirs', nargs=argparse.ZERO_OR_MORE, default=[],
                        help='Data dirs')
    parser.add_argument('--data-file-idx', dest='data_file_idx', action="store", type=int, default=None,
                        help='Index of the data file in the data dir')
    parser.add_argument('--data-file', dest='data_file', action="store", default=None,
                        help='Data file to process.')

    parser.add_argument('--limit', dest='limit', action="store", type=int, default=35,
                        help='1 << limit for the maximum factor')
    parser.add_argument('--timeout', dest='timeout', action="store", type=int, default=4*60,
                        help='Number of seconds for the factorization job')
    parser.add_argument('--job-time', dest='job_time', action="store", type=int, default=None,
                        help='Time allocated for the job')

    parser.add_argument('--num-keys', dest='num_keys', action="store", type=int, default=None,
                        help='Number of keys to factor')
    parser.add_argument('--num', dest='num', action="store", type=int, default=None,
                        help='Number of outputs to generate')
    parser.add_argument('--batch-idx', dest='batch_idx', action="store", type=int, default=0,
                        help='Batch index of primes to factor')
    parser.add_argument('--max-keys', dest='max_keys', action='store_const', const=True, default=False,
                        help='Compute as many keys as possible in the given time window')
    parser.add_argument('--qinv2', dest='qinv2', action='store_const', const=True, default=False,
                        help='Use optimized inversion algorithm')
    parser.add_argument('--cheng', dest='cheng', action='store_const', const=True, default=False,
                        help='Use Cheng xgcd instead of norms')

    parser.add_argument('--res-dir', dest='res_dir', action='store', default='.',
                        help='Result directory')
    parser.add_argument('--unpack', dest='unpack', action='store',
                        help='Unpack card keys')
    parser.add_argument('--file-dec', dest='file_dec', action="store", type=int, default=4,
                        help='File numbering decimal places')
    parser.add_argument('--key-count-only', dest='key_count_only', action='store_const', const=True, default=False,
                        help='Compute number of keys and terminate')

    parser.add_argument('--rand-prime', dest='rand_prime', action="store", type=int, default=None,
                        help='Random prime bitsize to test')

    parser.add_argument('--rand-type', dest='rand_type', action="store", type=int, default=None,
                        help='Random number type, None=0=classic, 1=(p-1) does not have 3 factor')

    parser.add_argument('--sample-file', dest='sample_file', action='store',
                        help='File with sampled D and corresponding class numbers')
    parser.add_argument('--disc', dest='disc', action='store', type=int, default=0,
                        help='D, the discriminant to compute factorization for')
    parser.add_argument('--prime-bits', dest='prime_bits', action='store', type=int, default=256,
                        help='Number of prime bits')
    parser.add_argument('--force', dest='force', action='store_const', const=True, default=False,
                        help='Ignore existing files')
    parser.add_argument('--test', dest='test', action='store_const', const=True, default=False,
                        help='Test implementation')
    parser.add_argument('--all-combs', dest='all_combs', action='store_const', const=True, default=False,
                        help='Test all factor combinations')
    parser.add_argument('--key-ids', dest='key_ids', nargs=argparse.ZERO_OR_MORE, default=[], type=int,
                        help='Key IDs')
    parser.add_argument('--random-keys', dest='random_keys', default=None, type=int,
                        help='Randomly generated keys')
    parser.add_argument('--random-keys-struct', dest='random_keys_struct', default=None,
                        help='JSON how random keys look like, [{bits:512, count:10000}]')
    parser.add_argument('--random-keys-struct-file', dest='random_keys_struct_file', default=None,
                        help='JSON how random keys look like, [{bits:512, count:10000}]')
    parser.add_argument('--keys-struct', dest='keys_struct', default=None,
                        help='JSON how keys look like, [{bits:512, count:10000}]')
    parser.add_argument('--keys-struct-file', dest='keys_struct_file', default=None,
                        help='JSON how keys look like, [{bits:512, count:10000}]')

    parser.add_argument('--known-d', dest='known_d', default=None,
                        help='known D-CN relations')
    parser.add_argument('--needed-d', dest='needed_d', default=None,
                        help='D-CN relations to compute')
    parser.add_argument('--needed-d-offset', dest='needed_d_offset', default=0, type=int,
                        help='D-CN relations to compute, offset')
    parser.add_argument('--needed-d-len', dest='needed_d_len', default=None, type=int,
                        help='D-CN relations to compute, len')

    parser.add_argument('--gen-moduli', dest='gen_moduli', action='store_const', const=True, default=False,
                        help='Generate whole moduli of 2*bitsize')
    parser.add_argument('--cm-primes', dest='cm_primes', action='store_const', const=True, default=False,
                        help='generate CM primes')

    parser.add_argument('--bgcd', dest='bgcd', default=None,
                        help='BGCD file to analyze')
    parser.add_argument('--bgcd-computed', dest='bgcd_computed', action='store_const', const=True, default=False,
                        help='check if bgcd has been computed already')
    parser.add_argument('--postfactor', dest='postfactor', action='store_const', const=True, default=False,
                        help='postfactorization - finish factorization of timed out values')

    parser.add_argument('--discs', dest='discs', nargs=argparse.ZERO_OR_MORE, default=[], type=int,
                        help='discs')
    parser.add_argument('--cns', dest='cns', nargs=argparse.ZERO_OR_MORE, default=[], type=int,
                        help='cns')

    parser.add_argument('--pm1', dest='pm1', action='store_const', const=True, default=False,
                        help='Compute only p-1, not 4p-1. For batch-GCD statistics')
    parser.add_argument('--no-D-phase', dest='no_d_phase', action='store_const', const=True, default=False,
                        help='Skips determinant checking phase after batch gcd phase')
    parser.add_argument('--bgcd-per-src', dest='bgcd_per_src', action='store_const', const=True, default=False,
                        help='Per source batch gcd, isolate among sources')

    args = parser.parse_args()
    if args.action is None or args.action == 'test_prime':
        work(args)
    elif args.action == 'sample':
        work_sample(args)
    elif args.action == 'factor':
        work_factor(args)
    elif args.action == 'batchgcd':
        work_batch_gcd(args)
    elif args.action == 'gen_prime':
        work_gen_prime(args)
    elif args.action == 'primorial_d':
        work_primorial_d(args)
    elif args.action == 'hilbert':
        work_hilbert(args)
    else:
        raise ValueError('Unknown action: %s' % args.action)


if __name__ == "__main__":
    main()


