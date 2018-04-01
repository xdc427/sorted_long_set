import java.util.*;

/**
 * Created by xdc on 16-8-30.
 */
/*
 * 如果是integer set在扩展的的时候可以根据数据多少变换为bitmap模式
 * 主要瓶颈在于内存的带宽（拷贝时的开销），但也足以支撑亿级别的数据量。
 * 可构造一棵完全树来统计非deleted bit数量，以实现按index来访问，64字节对齐
 *
 * |<--    main area    -->|<- cache area ->|
 *                         |                |
 *                         V                V
 *                      unmerged_index    cur_size
* */
public class Sorted_long_set1 {
    //等比例增加，每两次翻倍 (a+x)/x = 2a/(a-x)
    //空间利用率大于50%
    //每次增长大小
    private static final int[] GROW_N = {
            1,1,2,2,3,5,7,9,13,19,
            26,38,53,75,106,150,212,300,424,600,
            848,1200,1696,2400,3391,4801,6783,9601,13566,19202,
            27132,38404,54264,76808,108528,153616,217055,307233,434110,614466,
            868221,1228931,1736442,2457862,3472884,4915724,6945767,9831449,13891535,19662897,
            27783070,39325794,55566139,78651589,111132279,157303177,222264558,314606354,444529115,629212709,
            889058230,1258425418
    };
    private static final int MIN_REDUCE_SIZE = 256;
    private static final int CACHE_SIZE = 1024;
    private final int init_size; //初始大小
    private long[] deleted_map; //对应keys的位图，置1代表删除
    private long[] keys; //存储数据
    private int unmerged_index;
    private int cur_size;
    private int deleted_size; //当前所有deleted总数
    private byte grow_index; //当前对应的GROW_N下标

    private long move_num; //统计总移动次数查看性能

    public Sorted_long_set1(int init_size ){
        byte power;
        if( init_size <= 4 ){
            power = 2;
            this.init_size = 1 << power;
            grow_index = (byte)(2 * power - 3);//对应关系
        }else{
            power = (byte)(64 - Long.numberOfLeadingZeros(init_size-1));
            int tmp = 1 << power;
            grow_index = (byte)(2 * power - 3);
            if( tmp - GROW_N[grow_index] >= init_size ){
                this.init_size = tmp - GROW_N[grow_index--];
            }else{
                this.init_size = tmp;
            }
        }
        this.keys = new long[this.init_size];
        this.deleted_map = new long[((keys.length >>> 6) + ((keys.length & 0x3f)!=0?1:0))];
    }

    //README上计算是sqrt(2*size)移动次数最少,实际由于cache长度更小，叠加缓存效应sqrt(size)*2效果更佳
    private int cache_size( int size ){
        return (int)(Math.sqrt(size)*2);
    }

    private boolean is_deleted( int index ){
        if( index >= cur_size ){
            return false;
        }else{
            int data_index = index >>> 6;
            int bit_index = index & 0x3f;
            return ( deleted_map[data_index] & ( 1L << bit_index ) ) != 0;
        }
    }

    private void set_deleted( int index ){
        if( index < cur_size ){
            int data_index = index >>> 6;
            int bit_index = index & 0x3f;
            if( ( deleted_map[data_index] & ( 1L << bit_index ) ) == 0 ) {
                deleted_map[data_index] |= (1L << bit_index);
                deleted_size++;
            }
        }
    }

    private void clear_deleted( int index ){
        if( index < cur_size ){
            int data_index = index >>> 6;
            int bit_index = index & 0x3f;
            if( ( deleted_map[data_index] & ( 1L << bit_index ) ) != 0 ) {
                deleted_map[data_index] &= ~(1L << bit_index);
                deleted_size--;
            }
        }
    }

    private static void bit_copy( long[] src, int src_position,long[] dst,int dst_position,int len){
        int dst_index = dst_position >>> 6;
        int dst_bit_index = dst_position & 0x3f;
        int src_index = src_position >>> 6;
        int src_bit_index = src_position & 0x3f;
        long tmp;
        while (len > 0 ){
            int dst_len = Integer.min(len,64 - dst_bit_index);
            int src_len = 64 - src_bit_index;
            if( src_len >= dst_len ){
                tmp = ( src[src_index] >>> src_bit_index ) & (-1L >>> (64-dst_len));
                src_index += (src_bit_index + dst_len) >>> 6;
                src_bit_index = ( src_bit_index + dst_len ) & 0x3f;
            }else{
                tmp = src[src_index++] >>> src_bit_index;
                src_bit_index = dst_len - src_len;
                tmp |= (src[src_index] & (-1L >>> (64-src_bit_index)))<<src_len;
            }
            dst[dst_index] = ( dst[dst_index] & (~((-1L >>> (64 - dst_len)) << dst_bit_index)) )
                    | (tmp << dst_bit_index);
            dst_index++;
            dst_bit_index = 0;
            len -= dst_len;
        }
    }

    private static void bit_copy_reverse( long[] src,int src_last_position,long[] dst,int dst_last_position,int len){
        int dst_last_index = dst_last_position >>> 6;
        int dst_bit_last_index = dst_last_position & 0x3f;
        int src_last_index = src_last_position >>> 6;
        int src_last_bit_index = src_last_position & 0x3f;
        long tmp;
        while (len > 0 ){
            int dst_len = Integer.min(len,dst_bit_last_index+1);
            int src_len = src_last_bit_index + 1;
            if( src_len >= dst_len ){
                tmp = (src[src_last_index] << (63-src_last_bit_index)) & (-1L <<(64-dst_len));
                src_last_index -= 1 - ((src_last_bit_index + 64 - dst_len) >>> 6);
                src_last_bit_index = ( src_last_bit_index + 64 - dst_len ) & 0x3f;
            }else{
                tmp = src[src_last_index--] << (63-src_last_bit_index);
                src_last_bit_index = 63 - ( dst_len - src_len );
                tmp |= (src[src_last_index] & (-1L << (src_last_bit_index+1)))>>>src_len;
            }
            dst[dst_last_index] = ( dst[dst_last_index] & (~((-1L << (64 - dst_len)) >>> (63 - dst_bit_last_index))))
                    | (tmp >>> (63 - dst_bit_last_index));
            dst_last_index--;
            dst_bit_last_index = 63;
            len -= dst_len;
        }
    }

    private static int bit_scan( long[] data, int position, int len ){
        int index = position >>> 6;
        int bit_index = position & 0x3f;
        while (len > 0){
            int cur_len = Integer.min(64-bit_index,len);
            long tmp;
            if( ( (tmp = ( data[index] >>> bit_index ) & (-1L >>> (64 -cur_len)) )) != 0 ){
                return position + Long.numberOfTrailingZeros(tmp);
            }
            index++;
            bit_index = 0;
            position += cur_len;
            len -= cur_len;
        }
        return -1;
    }

    private void gc() {
        int i = 0;
        int save_index = 0;
        int new_unmerge_index = 0;

        while (i < cur_size) {
            if (i <= unmerged_index) {
                new_unmerge_index = save_index;
            }
            if (is_deleted(i)) {
                i++;
            } else {
                keys[save_index++] = keys[i++];
            }
        }
        deleted_size = 0;
        cur_size = save_index;
        unmerged_index = new_unmerge_index;
        Arrays.fill(deleted_map, 0);
    }

    //应该保留deleted，因为删掉并不会快多少，但提高了以后的命中率,保留变化
    //这段为了少分配一次内存写得太复杂了，版本二好多了
    private void merge() {
        int unmerged_size = cur_size - unmerged_index;
        long[] tmp = new long[unmerged_size + unmerged_size/64 + 2];
        System.arraycopy(keys, unmerged_index, tmp, 0, unmerged_size);
        bit_copy(deleted_map,unmerged_index,tmp,unmerged_size*64,unmerged_size);
        int deleted_index = (cur_size - 1) >>> 6, deleted_bit_index = (cur_size - 1) & 0x3f;
        int i_index = (unmerged_index-1) >>> 6,i_bit_index = (unmerged_index-1) & 0x3f;
        int k_index = unmerged_size + ((unmerged_size - 1) >>> 6),k_bit_index = (unmerged_size - 1) & 0x3f;
        int i = unmerged_index-1, k = unmerged_size -1;
        int save_index = cur_size -1;
        int mark_save_index = save_index;
        if( cur_size < unmerged_size * 8 ) {
            while (i >= 0 && k >= 0 ) {
                deleted_map[deleted_index] &= ~(1L << deleted_bit_index);
                if( tmp[k] >= keys[i] ){
                    keys[save_index--] = tmp[k--];
                    deleted_map[deleted_index] |= (( tmp[k_index] >>> k_bit_index ) & 0x1 ) << deleted_bit_index;
                    k_index -= 1- ((k_bit_index + 63) >>> 6);
                    k_bit_index = (k_bit_index + 63 ) & 0x3f;
                }else{
                    keys[save_index--] = keys[i--];
                    deleted_map[deleted_index] |= (( deleted_map[i_index] >>> i_bit_index ) & 0x1 ) << deleted_bit_index;
                    i_index -= 1- ((i_bit_index + 63) >>> 6);
                    i_bit_index = (i_bit_index + 63 ) & 0x3f;
                }
                deleted_index -= 1 - ( (deleted_bit_index + 63 ) >>> 6 );
                deleted_bit_index = ( deleted_bit_index + 63 ) & 0x3f;
            }
        }else{
            while (i >= 0 && k >= 0 ){
                if( tmp[k] >= keys[i] ){
                    keys[save_index--] = tmp[k--];
                    deleted_map[deleted_index] &= ~(1L << deleted_bit_index);
                    deleted_map[deleted_index] |= (( tmp[k_index] >>> k_bit_index ) & 0x1 ) << deleted_bit_index;
                    k_index -= 1- ((k_bit_index + 63) >>> 6);
                    k_bit_index = (k_bit_index + 63 ) & 0x3f;
                    deleted_index -= 1 - ( (deleted_bit_index + 63 ) >>> 6 );
                    deleted_bit_index = ( deleted_bit_index + 63 ) & 0x3f;
                }else{
                    int index = ~Arrays.binarySearch(keys,0,i+1,tmp[k]);
                    int len = i - index + 1;
                    System.arraycopy(keys,index,keys,save_index-len+1,len);
                    save_index -= len;
                    i -= len;
                    bit_copy_reverse(deleted_map,i_index*64+i_bit_index,deleted_map,deleted_index*64+deleted_bit_index,len);
                    i_index -= (len >>> 6)+ 1 - ((i_bit_index + 64 - (len & 0x3f)) >>> 6);
                    i_bit_index = (i_bit_index + 64 - (len & 0x3f)) & 0x3f;
                    deleted_index -= (len >>> 6) + 1 - ((deleted_bit_index + 64 - (len & 0x3f)) >>> 6);
                    deleted_bit_index = (deleted_bit_index + 64 - (len & 0x3f)) & 0x3f;
                }
            }
        }
        if( k >= 0 ){
            System.arraycopy(tmp,0,keys,save_index-k,k+1);
            bit_copy_reverse(tmp,k_index*64+k_bit_index,deleted_map,deleted_index*64+deleted_bit_index,k+1);
            save_index -= k+1;
            k -= k+1;
        }
        move_num += mark_save_index - save_index;
        unmerged_index = cur_size;
    }

    private void grow(){
        keys = Arrays.copyOf(keys, keys.length + GROW_N[++grow_index]);
        if( keys.length > deleted_map.length * 64 ) {
            deleted_map = Arrays.copyOf(deleted_map, (keys.length >>> 6) + ((keys.length & 0x3f)!=0?1:0));
        }
    }

    private void reduce() {
        long[] tmp = new long[keys.length - GROW_N[grow_index--]];
        int i = 0, k = unmerged_index;
        int save_index = 0;

        while (i < unmerged_index && k < cur_size) {
            if (is_deleted(i)) {
                i++;
            } else if (is_deleted(k)) {
                k++;
            } else {
                if (keys[i] < keys[k]) {
                    tmp[save_index++] = keys[i++];
                } else {
                    tmp[save_index++] = keys[k++];
                }
            }
        }
        while (i < unmerged_index) {
            if (is_deleted(i)) {
                i++;
            } else {
                tmp[save_index++] = keys[i++];
            }
        }
        while (k < cur_size) {
            if (is_deleted(k)) {
                k++;
            } else {
                tmp[save_index++] = keys[k++];
            }
        }
        deleted_map = new long[(keys.length >>> 6) + ((keys.length & 0x3f)!=0?1:0)];
        keys = tmp;
        cur_size = unmerged_index = save_index;
        deleted_size = 0;
    }

    public boolean contain( long id ){
        synchronized (this) {
            int i = Arrays.binarySearch(keys, 0, unmerged_index, id);
            if (i >= 0) {
                return !is_deleted(i);
            } else {
                i = Arrays.binarySearch(keys, unmerged_index, cur_size, id);
                return !(i < 0 || is_deleted(i));
            }
        }
    }

    private void insert_data( int index, long data ){
        if( index == cur_size ){
            keys[index] = data;
        }else {
            move_num += cur_size - index;
            System.arraycopy(keys, index, keys, index + 1, cur_size - index);
            keys[index] = data;
            bit_copy_reverse(deleted_map,cur_size-1,deleted_map,cur_size,cur_size-index);
        }
        cur_size++;
    }

    private void _add( long id ){
        int i,k,tmp;

        //搜索 main area 和 cache area，找到直接清除对应的deleted bit
        if( ( tmp = i = Arrays.binarySearch(keys,0,unmerged_index,id) ) >= 0
                || ( tmp = k = Arrays.binarySearch(keys,unmerged_index,cur_size,id) ) >= 0){
            clear_deleted(tmp);
        }else{
            i = ~i;
            k = ~k;
            //若没找到，但当前或前面的数据的deleted bit置了位，直接替换即可
            if( (is_deleted(tmp = i) && i < unmerged_index)
                    || is_deleted(tmp = k)
                    || ((tmp = i - 1 ) >= 0 && is_deleted(tmp))
                    || ((tmp = k - 1 ) >= unmerged_index && is_deleted(tmp))){
                keys[tmp] = id;
                clear_deleted(tmp);
                return;
            }

            //扫描main area 和 cache area 一段区域，512 和 256 不是精确计算的
            int index;
            if( (( tmp = bit_scan(deleted_map,i,Integer.min(unmerged_index-i,512)) ) >= 0 && (index = i) >= 0 )
                    || ((tmp = bit_scan(deleted_map,k,Integer.min(cur_size-k,256))) >= 0 && (index = k) >= 0 )){
                bit_copy_reverse(deleted_map,tmp-1,deleted_map,tmp,tmp-index);
                System.arraycopy(keys,index,keys,index+1,tmp-index);
                keys[index] = id;
                deleted_size--;
                return;
            }

            if( cur_size >= keys.length ){
                if( deleted_size >= GROW_N[grow_index] ){
                    gc();
                }else{
                    grow();
                }
                i = ~Arrays.binarySearch(keys,0,unmerged_index,id);
                k = ~Arrays.binarySearch(keys,unmerged_index,cur_size,id);
            }
            tmp = cache_size(cur_size);
            if( cur_size < CACHE_SIZE
                    && unmerged_index == cur_size ){
                insert_data(i,id);
                unmerged_index = cur_size;
            }else{
                insert_data(k,id);
                if( cur_size-unmerged_index >= tmp ){
                    merge();
                }
            }
        }
    }

    public void add( long id ){
        synchronized (this){
            _add(id);
        }
    }

    public void add( List<Long> ids ){
        synchronized (this){
            ids.forEach(this::_add);
        }
    }

    private void _remove( long id ){
        int i = Arrays.binarySearch(keys, 0, unmerged_index, id);
        if( i >= 0 ){
            set_deleted(i);
            if( keys.length >=MIN_REDUCE_SIZE
                    && keys.length > init_size
                    && deleted_size + (keys.length - cur_size) >= GROW_N[grow_index] + GROW_N[grow_index-1]){
                reduce();
            }
        }else{
            int k = Arrays.binarySearch(keys,unmerged_index,cur_size,id);
            if( k >= 0 ){
                set_deleted(k);
                if( keys.length >=MIN_REDUCE_SIZE
                        && keys.length > init_size
                        && deleted_size + (keys.length - cur_size) >= GROW_N[grow_index] + GROW_N[grow_index-1]){
                    reduce();
                }
            }
        }
    }

    public void remove( long id ){
        synchronized (this){
            _remove(id);
        }
    }

    public void remove( List<Long> ids ){
        synchronized (this){
            ids.forEach(this::_remove);
        }
    }

    public int size(){
        return cur_size - deleted_size;
    }

    public void print(){
        System.out.println("-------------");
        System.out.println("deleted_size:" + deleted_size);
        System.out.println("cur_size:" + cur_size);
        for( int i = 0; i < cur_size; i++ ){
            if(unmerged_index == i){
                System.out.print("|");
            }
            System.out.print(keys[i]);
            if(is_deleted(i)) {
                System.out.print("X");
            }
            System.out.print("  ");
        }
        System.out.println();
    }

    public static void randomTest( int num ){
        ArrayList<Long> arrayList = new ArrayList<>();
        Sorted_long_set1 sorted_long_set1 = new Sorted_long_set1(4);

        for( int i = 0; i < num; i++ ){
            arrayList.add((long)i);
        }

        int n = 0;
        for( long a : arrayList) {
            sorted_long_set1.add(a);
            assert sorted_long_set1.contain(a);
            sorted_long_set1.add(a);
            n++;
            assert sorted_long_set1.size() == n;
        }
        n = 0;
        for( long a : arrayList ){
            assert sorted_long_set1.contain(a);
            sorted_long_set1.remove(a);
            n++;
            assert sorted_long_set1.size() == arrayList.size() - n;
            assert !sorted_long_set1.contain(a);
            sorted_long_set1.remove(a);
        }
        Collections.shuffle(arrayList);
        n = 0;
        for( long a : arrayList) {
            sorted_long_set1.add(a);
            assert sorted_long_set1.contain(a);
            sorted_long_set1.add(a);
            n++;
            assert sorted_long_set1.size() == n;
        }
        Collections.shuffle(arrayList);
        n = 0;
        for( long a : arrayList ){
            assert sorted_long_set1.contain(a);
            sorted_long_set1.remove(a);
            n++;
            assert sorted_long_set1.size() == arrayList.size() - n;
            assert !sorted_long_set1.contain(a);
            sorted_long_set1.remove(a);
        }

        Collections.shuffle(arrayList);
        ArrayList<Long> delList = new ArrayList<>();
        for( long a : arrayList ){
            sorted_long_set1.add(a);
        }
        Collections.shuffle(arrayList);
        for( int i = 0; i <= arrayList.size()/2; i++ ){
            sorted_long_set1.remove(arrayList.get(i));
            delList.add(arrayList.get(i));
        }
        Collections.shuffle(arrayList);
        n = 0;
        for( long a : arrayList ){
            assert (!delList.contains(a) && sorted_long_set1.contain(a))
                    || (delList.contains(a) && !sorted_long_set1.contain(a));
            sorted_long_set1.add(a);
            if(delList.contains(a)) {
                n++;
            }
            assert sorted_long_set1.contain(a);
            assert sorted_long_set1.size() == arrayList.size() - delList.size() + n;
        }
        sorted_long_set1.remove(arrayList);


        assert sorted_long_set1.size() == 0;
        delList.clear();
        Collections.shuffle(arrayList);
        n = 0;
        //arrayList.forEach(a->System.out.print(a+" "));
        //System.out.println(" begin ");
        for( long a : arrayList ){
            sorted_long_set1.add(a);
            delList.add(a);
            n++;
            //System.out.println(a);
            //sorted_long_set1.print();
            if (delList.size() > 10 ) {
                List<Long> list = delList.subList(delList.size() - 5, delList.size());
                //list.forEach(b->System.out.print(b+" "));
                //System.out.println();
                for ( long b : list ){
                    assert sorted_long_set1.contain(b);
                    sorted_long_set1.remove(b);
                    assert !sorted_long_set1.contain(b);
                    //sorted_long_set1.print();
                }
                n -= list.size();
                delList.clear();
            }
            assert sorted_long_set1.size() == n;
        }
    }

    public static void main( String[] args ){
        /*
        //正确性测试,Edit Configurations->VM options 加上-ea,允许assert
        for( int i = 1; i < 10000; i++ ){
            randomTest(i);
            System.out.println(i);
        }
        System.out.println("random test sucess");
        */

        //性能比对测试
        long start_time = System.currentTimeMillis();
        for( int j =0; j < 4; j++ ) {
            HashSet<Long> hashSet = new HashSet<>();
            for (int i = 0; i < 10000000; i++) {
                hashSet.add((long) i);
            }

            for( int i = 0; i < 10000000; i++ ){
                hashSet.remove((long)i);
            }
        }
        long end_time = System.currentTimeMillis();
        System.out.println("HashSet:"+(end_time - start_time) + "ms");


        //cpu降点温
        try {
            Thread.sleep(30000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        //逆序是这个算法最差表现
        start_time = System.currentTimeMillis();
        for( int j =0; j < 4; j++ ) {
            Sorted_long_set1 sorted_long_set1 = new Sorted_long_set1(4);
            for (int i = 10000000 - 1; i >= 0; i--) {
                sorted_long_set1.add(i);
            }
            System.out.println("move_num:"+ sorted_long_set1.move_num);

            for( int i = 0; i < 10000000; i++ ){
                sorted_long_set1.remove(i);
            }
        }
        end_time = System.currentTimeMillis();
        System.out.println("Sorted_long_set1:"+(end_time - start_time) + "ms");

    }
}
