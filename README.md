    这是个节省内存的紧凑的map实现，功能类似于HashSet.暂时适用于key为固定长度的map，
像long，int等。提供了add，remove，contain，size方法实现。目前主要场景是为了节省内
存，也是初衷，虽然也有不错的性能。
    版本1是原始版本（sorted_long_set1），最初的想法是想用一个排序数组做，但是如果
数组大了，每次插入的移动次数会不可接受，这也是以后主要要解决的问题，这个版本的解决
方案是用两个排序数组，一个大的一个小的，先插入小的小的满了再合并到大的。那小的多大
合适,大的长为n，假设小的为m，那么考虑把小的m填满然后合并到大的用了多少移动次数，小
的填满最差用 m*m/2,合并到大的用 n + m,m << n 所以为n，总数为 m*m/2 + n,平均每个需要 
（m*m/2 + n)/m = n/m + m/2 ，求最优值m = sqrt(2*n).那么最优平均移动次数为sqrt(2*n).
其他优化包括删除时只标记，以及一些数组扩容及缩小策略,在代码里有注释。
    版本2是个实验版本（sorted_long_set2），考虑了用两组这样的结构会有什么效果。这时
每个大的长n/2,假设每个小的还是长m,把m填满还是需要 m*m/2,合并到大的需要 n/2 + m,m<<n
所以为 n/2,总数为 m*m/2 + n/2,平均每个需要 m/2 + n/(2*m),最优值为 m = sqrt(n),那么最
优平移动次数为sqrt(n),移动次数为版本1的 1/sqrt(2) 。
   版本3暂时未实现（sorted_long_set3），这个版本要讨论用几组这样的结构可以达到最佳性
能。版本3将采用环形数组将每组结构连起来，这样方便在组与组之间移动少量数据来平衡而不
需要移动整个组的数据，这点最为关键。接下来还是计算最优值。数据总长度为n，组数为x，每组
带有的小排序数组长度为m, 每组内带有的大排序数组长度为n/x。把m填满最差用 m*m/2，合并到
组内大数组用 n/x + m,m << n/x 所以为 n/x,接下来还有一步，要把m平均到每个组，需要m*x/2
（这就是为什么用环型数组），总数为 m*m/2 + n/x + m*x/2 ，平均每个需要 m/2 + n/(m*x) +
x/2 ,求最优值m = power(n,1/3), x = power(n,1/3), 最优平均移动次数为 2*power(n,1/3).
在数据量大的情况性能会比前两个版本有量级提高，应该可以战胜HashSet。其实还有个大的提高，
前面两个版本由于块小，在数据扩大和缩小时会变慢，不那么均衡，版本3可以把组的扩大和缩小
分解到到后续一系列的操作中，以均衡性能。

