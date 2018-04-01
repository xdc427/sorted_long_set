import java.util.*;

/**
 * Created by xdc on 16-9-5.
 */
/*
* 版本2是个实验性的版本，分割成两个块，使平均移动次数变为原来的1/sqrt(2)，
* 耗时也相应缩小。接下来的版本是用环形缓冲区构建一个多块结构，那平衡开销会增大，
* 与块的数量成正比。在少数块的情况下，每增加一倍的块会使移动次数变为原来的1/sqrt(2)。
* 统计deleted的完全树是绝对寻址的，开销与其他操作成正比.
*
* |main A area-->               <--main B area|cache A area->                <-cache B area|
*               |               |             |             |                |
*               V               V             V             V                V
*          first_index       bottom_index  cache_offset  cache_first_index  cache_bottom_index
 */
public class Sorted_long_set2 {
    //等比例增加，每两次翻倍。 (a+x)/x = 2a/(a-x)
    //空间利用率大于50%
    private static final int[] GROW_N = {
            1, 1, 2, 2, 3, 5, 7, 9, 13, 19,
            26, 38, 53, 75, 106, 150, 212, 300, 424, 600,
            848, 1200, 1696, 2400, 3391, 4801, 6783, 9601, 13566, 19202,
            27132, 38404, 54264, 76808, 108528, 153616, 217055, 307233, 434110, 614466,
            868221, 1228931, 1736442, 2457862, 3472884, 4915724, 6945767, 9831449, 13891535, 19662897,
            27783070, 39325794, 55566139, 78651589, 111132279, 157303177, 222264558, 314606354, 444529115, 629212709,
            889058230, 1258425418
    };
    private static final int MIN_REDUCE_SIZE = 256;
    private static final byte BALANCE_LIMIT = 10;  //balance绝对值大于10触发平衡
    private final int init_size;
    private byte grow_index;
    private long[] deleted_map;
    private int deleted_size;
    private long[] keys;
    private int first_index;
    private int bottom_index;
    private int cache_offset;
    private int cache_first_index;
    private int cache_bottom_index;
    private long middle_key; //分割main A 和 main B，若无数据则为Long.MAX_VALUE
    private byte balance; //cache A合并到main A 加一，cache B 合并到 main B 减一

    private long move_num;

    public Sorted_long_set2(int init_size) {
        byte power;
        if (init_size <= 4) {
            power = 2;
            this.init_size = 1 << power;
            grow_index = (byte) (2 * power - 3);
        } else {
            power = (byte) (64 - Long.numberOfLeadingZeros(init_size - 1));
            int tmp = 1 << power;
            grow_index = (byte) (2 * power - 3);
            if (tmp - GROW_N[grow_index] >= init_size) {
                this.init_size = tmp - GROW_N[grow_index--];
            } else {
                this.init_size = tmp;
            }
        }
        int cache_size = (int) Math.round(Math.sqrt(this.init_size)) * 2;
        keys = new long[this.init_size + cache_size];
        first_index = 0;
        bottom_index = this.init_size - 1;
        cache_offset = this.init_size;
        cache_first_index = cache_offset;
        cache_bottom_index = keys.length - 1;
        deleted_map = new long[(keys.length >>> 6) + ((keys.length & 0x3f) != 0 ? 1 : 0)];
        middle_key = Long.MAX_VALUE;
    }

    /*
    * README上计算是sqrt(size)移动次数最少,实际由于cache长度更小，叠加缓存效应sqrt(2*size)效果更佳
    * 然后有两块再乘以2
    * */
    private int cache_size( int size ){
        return (int) Math.round(Math.sqrt(2*size)) * 2;
    }

    private boolean is_deleted(int position) {
        return (deleted_map[position >>> 6] & (1L << (position & 0x3f))) != 0;
    }

    private void set_deleted(int position) {
        int data_index = position >>> 6;
        int bit_index = position & 0x3f;
        if ((deleted_map[data_index] & (1L << bit_index)) == 0) {
            deleted_map[data_index] |= (1L << bit_index);
            deleted_size++;
            if (keys.length >= MIN_REDUCE_SIZE
                    && keys.length > init_size
                    && deleted_size + (bottom_index - first_index + 1)
                    - (cache_first_index - cache_offset) - (keys.length - cache_bottom_index - 1)
                    >= GROW_N[grow_index] + GROW_N[grow_index - 1]) {
                reduce();
            }
        }
    }

    private void clear_deleted(int position) {
        int data_index = position >>> 6;
        int bit_index = position & 0x3f;
        if ((deleted_map[data_index] & (1L << bit_index)) != 0) {
            deleted_map[data_index] &= ~(1L << bit_index);
            deleted_size--;
        }
    }

    private void move_deleted(int src_position, int dst_position) {
        int dst_index = dst_position >>> 6;
        int dst_bit_index = dst_position & 0x3f;
        int src_index = src_position >>> 6;
        int src_bit_index = src_position & 0x3f;
        deleted_map[dst_index] = (deleted_map[dst_index] & (~(1L << dst_bit_index)))
                | (((deleted_map[src_index] >>> src_bit_index) & 0x1L) << dst_bit_index);
    }

    private void init_deleted( int position ){
        deleted_map[position>>>6] &= ~(1L << (position & 0x3f));
    }

    private static void bit_copy(long[] src, int src_position, long[] dst, int dst_position, int len) {
        int dst_index = dst_position >>> 6;
        int dst_bit_index = dst_position & 0x3f;
        int src_index = src_position >>> 6;
        int src_bit_index = src_position & 0x3f;
        long tmp;
        while (len > 0) {
            int dst_len = Integer.min(len, 64 - dst_bit_index);
            int src_len = 64 - src_bit_index;
            if (src_len >= dst_len) {
                tmp = (src[src_index] >>> src_bit_index) & (-1L >>> (64 - dst_len));
                src_index += (src_bit_index + dst_len) >>> 6;
                src_bit_index = (src_bit_index + dst_len) & 0x3f;
            } else {
                tmp = src[src_index++] >>> src_bit_index;
                src_bit_index = dst_len - src_len;
                tmp |= (src[src_index] & (-1L >>> (64 - src_bit_index))) << src_len;
            }
            dst[dst_index] = (dst[dst_index] & (~((-1L >>> (64 - dst_len)) << dst_bit_index)))
                    | (tmp << dst_bit_index);
            dst_index++;
            dst_bit_index = 0;
            len -= dst_len;
        }
    }

    private static void bit_copy_reverse(long[] src, int src_last_position, long[] dst, int dst_last_position, int len) {
        int dst_last_index = dst_last_position >>> 6;
        int dst_bit_last_index = dst_last_position & 0x3f;
        int src_last_index = src_last_position >>> 6;
        int src_last_bit_index = src_last_position & 0x3f;
        long tmp;
        while (len > 0) {
            int dst_len = Integer.min(len, dst_bit_last_index + 1);
            int src_len = src_last_bit_index + 1;
            if (src_len >= dst_len) {
                tmp = (src[src_last_index] << (63 - src_last_bit_index)) & (-1L << (64 - dst_len));
                src_last_index -= 1 - ((src_last_bit_index + 64 - dst_len) >>> 6);
                src_last_bit_index = (src_last_bit_index + 64 - dst_len) & 0x3f;
            } else {
                tmp = src[src_last_index--] << (63 - src_last_bit_index);
                src_last_bit_index = 63 - (dst_len - src_len);
                tmp |= (src[src_last_index] & (-1L << (src_last_bit_index + 1))) >>> src_len;
            }
            dst[dst_last_index] = (dst[dst_last_index] & (~((-1L << (64 - dst_len)) >>> (63 - dst_bit_last_index))))
                    | (tmp >>> (63 - dst_bit_last_index));
            dst_last_index--;
            dst_bit_last_index = 63;
            len -= dst_len;
        }
    }

    private static int bit_scan(long[] data, int position, int len) {
        int index = position >>> 6;
        int bit_index = position & 0x3f;
        long tmp;

        while (len > 0) {
            int cur_len = Integer.min(64 - bit_index, len);
            if (((tmp = (data[index] >>> bit_index) & (-1L >>> (64 - cur_len)))) != 0) {
                return position + Long.numberOfTrailingZeros(tmp);
            }
            index++;
            bit_index = 0;
            position += cur_len;
            len -= cur_len;
        }
        return -1;
    }

    private static int bit_scan_reverse(long[] data, int last_position, int len) {
        int index = last_position >>> 6;
        int bit_index = last_position & 0x3f;
        long tmp;

        while (len > 0) {
            int cur_len = Integer.min(bit_index + 1, len);
            if ((tmp = (data[index] << (63 - bit_index)) & (-1L << (64 - cur_len))) != 0) {
                return last_position - Long.numberOfLeadingZeros(tmp);
            }
            index--;
            bit_index = 63;
            last_position -= cur_len;
            len -= cur_len;
        }
        return -1;
    }

    //forward_len 包含middle_position,reverse_len 不包涵middle_position
    private static int bit_scan_2way(long[] data, final int middle_position, int forward_len, int reverse_len) {
        int forward_index = middle_position >>> 6;
        int forward_bit_index = middle_position & 0x3f;
        int reverse_index = (middle_position - 1) >>> 6;
        int reverse_bit_index = (middle_position -1) & 0x3f;
        int forward_position = middle_position;
        int reverse_position = middle_position -1;
        long tmp;
        int position = -1;

        while (forward_len > 0 && reverse_len > 0) {
            int cur_forward_len = Integer.min(64 - forward_bit_index, forward_len);
            if (((tmp = (data[forward_index] >>> forward_bit_index) & (-1L >>> (64 - cur_forward_len)))) != 0) {
                position = forward_position + Long.numberOfTrailingZeros(tmp);
                forward_len = 0;
                reverse_len = Integer.min(reverse_len, position + reverse_position - middle_position * 2);
                break;
            }
            int cur_reverse_len = Integer.min(reverse_bit_index + 1, reverse_len);
            if ((tmp = (data[reverse_index] << (63 - reverse_bit_index)) & (-1L << (64 - cur_reverse_len))) != 0) {
                position = reverse_position - Long.numberOfLeadingZeros(tmp);
                reverse_len = 0;
                forward_len = Integer.min(forward_len, middle_position * 2 - position - forward_position);
                break;
            }
            forward_index++;
            forward_bit_index = 0;
            reverse_index--;
            reverse_bit_index = 63;
            forward_position += cur_forward_len;
            reverse_position -= cur_reverse_len;
            forward_len -= cur_forward_len;
            reverse_len -= cur_reverse_len;
        }
        while (forward_len > 0) {
            int cur_len = Integer.min(64 - forward_bit_index, forward_len);
            if (((tmp = (data[forward_index] >>> forward_bit_index) & (-1L >>> (64 - cur_len)))) != 0) {
                return forward_position + Long.numberOfTrailingZeros(tmp);
            }
            forward_index++;
            forward_bit_index = 0;
            forward_position += cur_len;
            forward_len -= cur_len;
        }
        while (reverse_len > 0) {
            int cur_len = Integer.min(reverse_bit_index + 1, reverse_len);
            if ((tmp = (data[reverse_index] << (63 - reverse_bit_index)) & (-1L << (64 - cur_len))) != 0) {
                return reverse_position - Long.numberOfLeadingZeros(tmp);
            }
            reverse_index--;
            reverse_bit_index = 63;
            reverse_position -= cur_len;
            reverse_len -= cur_len;
        }
        return position;
    }

    private void gc() {
        int save_index;

        save_index = 0;
        for (int i = 0; i < first_index; i++) {
            if (!is_deleted(i)) {
                keys[save_index++] = keys[i];
            }
        }
        first_index = save_index;

        save_index = cache_offset - 1;
        for (int i = cache_offset - 1; i > bottom_index; i--) {
            if (!is_deleted(i)) {
                keys[save_index--] = keys[i];
            }
        }
        bottom_index = save_index;

        save_index = cache_offset;
        for (int i = cache_offset; i < cache_first_index; i++) {
            if (!is_deleted(i)) {
                keys[save_index++] = keys[i];
            }
        }
        cache_first_index = save_index;

        save_index = keys.length - 1;
        for (int i = keys.length - 1; i > cache_bottom_index; i--) {
            if (!is_deleted(i)) {
                keys[save_index--] = keys[i];
            }
        }
        cache_bottom_index = save_index;

        Arrays.fill(deleted_map, 0L);
        deleted_size = 0;
        balance = BALANCE_LIMIT + 1;//下一次merge一定会重新平衡
    }

    private void balance() {
        if (balance >= BALANCE_LIMIT
                || balance <= -BALANCE_LIMIT) {
            int bottom_len = cache_offset - bottom_index - 1;
            int ave_len = (first_index + bottom_len + 1) / 2;
            if (first_index > ave_len) {
                int copy_len = first_index - ave_len;
                System.arraycopy(keys, first_index - copy_len, keys, bottom_index - copy_len + 1, copy_len);
                bit_copy_reverse(deleted_map, first_index - 1, deleted_map, bottom_index, copy_len);
                first_index -= copy_len;
                bottom_index -= copy_len;
                middle_key = first_index > 0 ? keys[first_index - 1] : Long.MAX_VALUE;
                int index = Arrays.binarySearch(keys, cache_offset, cache_first_index, middle_key);
                index = index >= 0 ? index + 1 : ~index;
                copy_len = cache_first_index - index;
                if (copy_len > 0) {
                    System.arraycopy(keys, index, keys, cache_bottom_index - copy_len + 1, copy_len);
                    bit_copy_reverse(deleted_map, cache_first_index - 1, deleted_map, cache_bottom_index, copy_len);
                    cache_first_index -= copy_len;
                    cache_bottom_index -= copy_len;
                }
                move_num += copy_len;
            } else if (first_index < ave_len) {
                int copy_len = ave_len - first_index;
                System.arraycopy(keys, bottom_index + 1, keys, first_index, copy_len);
                bit_copy(deleted_map, bottom_index + 1, deleted_map, first_index, copy_len);
                first_index += copy_len;
                bottom_index += copy_len;
                middle_key = first_index > 0 ? keys[first_index - 1] : Long.MAX_VALUE;
                int index = Arrays.binarySearch(keys, cache_bottom_index + 1, keys.length, middle_key);
                index = index >= 0 ? index : (~index) - 1;
                copy_len = index - cache_bottom_index;
                if (copy_len > 0) {
                    System.arraycopy(keys, cache_bottom_index + 1, keys, cache_first_index, copy_len);
                    bit_copy(deleted_map, cache_bottom_index + 1, deleted_map, cache_first_index, copy_len);
                    cache_first_index += copy_len;
                    cache_bottom_index += copy_len;
                }
                move_num += copy_len;
            }
            balance = 0;
        }
    }

    //应该保留deleted，因为删掉并不会快多少，但提高了以后的命中率,保留变化
    private void merge() {
        int i, k;
        int save_index, mark_save_index;

        int merge_limit = ( keys.length - cache_offset ) /2;
        int cache_len, base_len;
        if ((cache_len = cache_first_index - cache_offset) >= merge_limit) {
            base_len = first_index;
            mark_save_index = save_index = first_index - 1 + cache_len;
            i = first_index - 1;
            k = cache_first_index - 1;
            if (base_len <= cache_len * 8) {
                while (i >= 0 && k >= cache_offset) {
                    if (keys[k] >= keys[i]) {
                        move_deleted(k, save_index);
                        keys[save_index--] = keys[k--];
                    } else {
                        move_deleted(i, save_index);
                        keys[save_index--] = keys[i--];
                    }
                }
            } else {
                while (i >= 0 && k >= cache_offset) {
                    if (keys[k] >= keys[i]) {
                        move_deleted(k, save_index);
                        keys[save_index--] = keys[k--];
                    } else {
                        int index = ~Arrays.binarySearch(keys, 0, i + 1, keys[k]);
                        int len = i - index + 1;
                        System.arraycopy(keys, index, keys, save_index - len + 1, len);
                        bit_copy_reverse(deleted_map, i, deleted_map, save_index, len);
                        save_index -= len;
                        i -= len;
                    }
                }
            }
            if( k >= cache_offset ){
                int copy_len = k - cache_offset +1;
                bit_copy_reverse(deleted_map,k,deleted_map,save_index,copy_len);
                System.arraycopy(keys,cache_offset,keys,save_index-copy_len+1,copy_len);
                save_index -= copy_len;
                k -= copy_len;
            }
            move_num += mark_save_index - save_index;
            first_index += cache_len;
            cache_first_index = cache_offset;
            balance--;
            balance();
        } else if ((cache_len = keys.length - cache_bottom_index - 1) >= merge_limit) {
            base_len = cache_offset - bottom_index - 1;
            mark_save_index = save_index = bottom_index - cache_len + 1;
            i = bottom_index + 1;
            k = cache_bottom_index + 1;
            if (base_len <= 8 * cache_len) {
                while (i < cache_offset && k < keys.length) {
                    if (keys[k] <= keys[i]) {
                        move_deleted(k, save_index);
                        keys[save_index++] = keys[k++];
                    } else {
                        move_deleted(i, save_index);
                        keys[save_index++] = keys[i++];
                    }
                }
            } else {
                while (i < cache_offset && k < keys.length) {
                    if (keys[k] <= keys[i]) {
                        move_deleted(k, save_index);
                        keys[save_index++] = keys[k++];
                    } else {
                        int index = ~Arrays.binarySearch(keys, i, cache_offset, keys[k]);
                        int len = index - i;
                        System.arraycopy(keys, i, keys, save_index, len);
                        bit_copy(deleted_map, i, deleted_map, save_index, len);
                        save_index += len;
                        i += len;
                    }
                }
            }
            if( k < keys.length ){
                int copy_len = keys.length -k;
                bit_copy(deleted_map,k,deleted_map,save_index,copy_len);
                System.arraycopy(keys,k,keys,save_index,copy_len);
                save_index += copy_len;
                k += copy_len;
            }
            move_num += save_index - mark_save_index;
            bottom_index -= cache_len;
            cache_bottom_index = keys.length - 1;
            balance++;
            balance();
        }
    }

    private void grow() {
        int new_size = cache_offset + GROW_N[++grow_index];
        int cache_size = cache_size(new_size);
        long[] tmp = new long[new_size + cache_size];
        long[] tmp_deleted_map = new long[(tmp.length >>> 6) + ((tmp.length & 0x3f) != 0 ? 1 : 0)];

        move_num += first_index + ( cache_offset - bottom_index - 1) + ( cache_first_index - cache_offset )
                + (keys.length - cache_bottom_index - 1);
        System.arraycopy(keys, 0, tmp, 0, first_index);
        bit_copy(deleted_map, 0, tmp_deleted_map, 0, first_index);
        int copy_len = cache_offset - bottom_index - 1;
        if (copy_len > 0) {
            System.arraycopy(keys, bottom_index + 1, tmp, new_size - copy_len, copy_len);
            bit_copy(deleted_map, bottom_index + 1, tmp_deleted_map, new_size - copy_len, copy_len);
        }
        bottom_index = new_size - copy_len - 1;

        copy_len = cache_first_index - cache_offset;
        System.arraycopy(keys, cache_offset, tmp, new_size, copy_len);
        bit_copy(deleted_map, cache_offset, tmp_deleted_map, new_size, copy_len);
        cache_first_index = new_size + copy_len;
        copy_len = keys.length - cache_bottom_index - 1;
        if (copy_len > 0) {
            System.arraycopy(keys, cache_bottom_index + 1, tmp, tmp.length - copy_len, copy_len);
            bit_copy(deleted_map, cache_bottom_index + 1, tmp_deleted_map, tmp.length - copy_len, copy_len);
        }
        cache_bottom_index = tmp.length - copy_len - 1;

        cache_offset = new_size;
        keys = tmp;
        deleted_map = tmp_deleted_map;
    }

    private void reduce() {
        int new_size = cache_offset - GROW_N[grow_index--];
        int cache_size = cache_size(new_size);
        long[] tmp = new long[new_size + cache_size];
        int i, k;
        int save_first_index, save_bottom_index;

        i = save_first_index = 0;
        k = cache_offset;
        for (; i < first_index && is_deleted(i); i++) ;
        if (i >= first_index) {
            for (; k < cache_first_index; k++) {
                if (!is_deleted(k)) {
                    tmp[save_first_index++] = keys[k];
                }
            }
        } else {
            all:
            while (true) {
                while (true) {
                    if (k >= cache_first_index) {
                        for (; i < first_index; i++) {
                            if (!is_deleted(i)) {
                                tmp[save_first_index++] = keys[i];
                            }
                        }
                        break all;
                    } else if (is_deleted(k)) {
                        k++;
                    } else if (keys[k] <= keys[i]) {
                        tmp[save_first_index++] = keys[k++];
                    } else {
                        tmp[save_first_index++] = keys[i++];
                        break;
                    }
                }
                while (true) {
                    if (i >= first_index) {
                        for (; k < cache_first_index; k++) {
                            if (!is_deleted(k)) {
                                tmp[save_first_index++] = keys[k];
                            }
                        }
                        break all;
                    } else if (is_deleted(i)) {
                        i++;
                    } else if (keys[i] <= keys[k]) {
                        tmp[save_first_index++] = keys[i++];
                    } else {
                        tmp[save_first_index++] = keys[k++];
                        break;
                    }
                }
            }
        }
        i = cache_offset - 1;
        k = keys.length - 1;
        save_bottom_index = new_size - 1;
        for (; i > bottom_index && is_deleted(i); i--) ;
        if (i <= bottom_index) {
            for (; k > cache_bottom_index; k--) {
                if (!is_deleted(k)) {
                    tmp[save_bottom_index--] = keys[k];
                }
            }
        } else {
            all:
            while (true) {
                while (true) {
                    if (k <= cache_bottom_index) {
                        for (; i > bottom_index; i--) {
                            if (!is_deleted(i)) {
                                tmp[save_bottom_index--] = keys[i];
                            }
                        }
                        break all;
                    } else if (is_deleted(k)) {
                        k--;
                    } else if (keys[k] >= keys[i]) {
                        tmp[save_bottom_index--] = keys[k--];
                    } else {
                        tmp[save_bottom_index--] = keys[i--];
                        break;
                    }
                }
                while (true) {
                    if (i <= bottom_index) {
                        for (; k > cache_bottom_index; k--) {
                            if (!is_deleted(k)) {
                                tmp[save_bottom_index--] = keys[k];
                            }
                        }
                        break all;
                    } else if (is_deleted(i)) {
                        i--;
                    } else if (keys[i] >= keys[k]) {
                        tmp[save_bottom_index--] = keys[i--];
                    } else {
                        tmp[save_bottom_index--] = keys[k--];
                        break;
                    }
                }
            }
        }
        int bottom_len = new_size - save_bottom_index - 1;
        int ave_len = (save_first_index + bottom_len + 1) / 2;
        if (save_first_index > ave_len) {
            int copy_len = save_first_index - ave_len;
            save_first_index -= copy_len;
            save_bottom_index -= copy_len;
            System.arraycopy(tmp, save_first_index, tmp, save_bottom_index + 1, copy_len);
        } else if (save_first_index < ave_len) {
            int copy_len = ave_len - save_first_index;
            System.arraycopy(tmp, save_bottom_index + 1, tmp, save_first_index, copy_len);
            save_first_index += copy_len;
            save_bottom_index += copy_len;
        }
        keys = tmp;
        first_index = save_first_index;
        bottom_index = save_bottom_index;
        cache_offset = new_size;
        cache_first_index = cache_offset;
        cache_bottom_index = keys.length - 1;
        middle_key = first_index > 0 ? keys[first_index - 1] : Long.MAX_VALUE;
        deleted_map = new long[(keys.length >>> 6) + ((keys.length & 0x3f) != 0 ? 1 : 0)];
        deleted_size = 0;
        balance = 0;
    }

    public boolean contain(long id) {
        synchronized (this) {
            int i;

            if (id <= middle_key) {
                return ((i = Arrays.binarySearch(keys, cache_offset, cache_first_index, id)) >= 0
                        || (i = Arrays.binarySearch(keys, 0, first_index, id)) >= 0)
                        && !is_deleted(i);
            } else {
                return ((i = Arrays.binarySearch(keys, cache_bottom_index + 1, keys.length, id)) >= 0
                        || (i = Arrays.binarySearch(keys, bottom_index + 1, cache_offset, id)) >= 0)
                        && !is_deleted(i);
            }
        }
    }

    private void replace_data(long data, int from_position, int to_position) {
        if (from_position == to_position
                || from_position == to_position + 1) {
            clear_deleted(to_position);
            keys[to_position] = data;
        } else if (to_position > from_position) {
            bit_copy_reverse(deleted_map, to_position - 1, deleted_map, to_position, to_position - from_position);
            System.arraycopy(keys, from_position, keys, from_position + 1, to_position - from_position);
            keys[from_position] = data;
            deleted_size--;
        } else {
            bit_copy(deleted_map, to_position + 1, deleted_map, to_position, from_position - to_position - 1);
            System.arraycopy(keys, to_position + 1, keys, to_position, from_position - to_position - 1);
            keys[from_position - 1] = data;
            deleted_size--;
        }
    }

    private void _add(long id) {
        int i, k, tmp;

        int cache_size = (keys.length - cache_offset) / 2;
        if (id <= middle_key) {
            if ((tmp = k = Arrays.binarySearch(keys, cache_offset, cache_first_index, id)) >= 0
                    || (tmp = i = Arrays.binarySearch(keys, 0, first_index, id)) >= 0) {
                clear_deleted(tmp);
                return;
            }
            i = ~i;
            k = ~k;
            if ((tmp = bit_scan_2way(deleted_map, k
                    , Integer.min(cache_first_index - k, cache_size / 2 + 8), Integer.min(k - cache_offset, cache_size / 8 + 8))) >= 0) {
                replace_data(id, k, tmp);
                return;
            }
            if ((tmp = bit_scan_2way(deleted_map, i
                    , Integer.min(first_index - i, cache_size / 2 + 8), Integer.min(i, cache_size / 8 + 8))) >= 0) {
                replace_data(id, i, tmp);
                return;
            }
            if ((bottom_index - first_index + 1) <= (cache_first_index - cache_offset) + (keys.length - cache_bottom_index - 1)) {
                if (deleted_size >= GROW_N[grow_index]) {
                    gc();
                } else {
                    grow();
                }
                k = ~Arrays.binarySearch(keys, cache_offset, cache_first_index, id);
            }
            if (k == cache_first_index) {
                init_deleted(cache_first_index);
                keys[cache_first_index++] = id;
            } else {
                move_num += cache_first_index - k;
                bit_copy_reverse(deleted_map, cache_first_index - 1, deleted_map, cache_first_index, cache_first_index - k);
                System.arraycopy(keys, k, keys, k + 1, cache_first_index - k);
                keys[k] = id;
                cache_first_index++;
            }
        } else {
            if ((tmp = k = Arrays.binarySearch(keys, cache_bottom_index + 1, keys.length, id)) >= 0
                    || (tmp = i = Arrays.binarySearch(keys, bottom_index + 1, cache_offset, id)) >= 0) {
                clear_deleted(tmp);
                return;
            }
            i = ~i;
            k = ~k;
            if ((tmp = bit_scan_2way(deleted_map, k, Integer.min(keys.length - k
                    , cache_size / 8 + 8), Integer.min(k - cache_bottom_index - 1, cache_size / 2 + 8))) >= 0) {
                replace_data(id, k, tmp);
                return;
            }
            if ((tmp = bit_scan_2way(deleted_map, i, Integer.min(cache_offset - i
                    , cache_size / 8 + 8), Integer.min(i - bottom_index - 1, cache_size / 2 + 8))) >= 0) {
                replace_data(id, i, tmp);
                return;
            }
            if ((bottom_index - first_index + 1) <= (cache_first_index - cache_offset) + (keys.length - cache_bottom_index - 1)) {
                if (deleted_size >= GROW_N[grow_index]) {
                    gc();
                } else {
                    grow();
                }
                k = ~Arrays.binarySearch(keys, cache_bottom_index + 1, keys.length, id);
            }
            if (k == cache_bottom_index + 1) {
                init_deleted(cache_bottom_index);
                keys[cache_bottom_index--] = id;
            } else {
                move_num += k - cache_bottom_index - 1;
                bit_copy(deleted_map, cache_bottom_index + 1, deleted_map, cache_bottom_index, k - cache_bottom_index - 1);
                System.arraycopy(keys, cache_bottom_index + 1, keys, cache_bottom_index, k - cache_bottom_index - 1);
                keys[k - 1] = id;
                cache_bottom_index--;
            }
        }
        merge();
    }

    public void add(long id) {
        synchronized (this) {
            _add(id);
        }
    }

    public void add(List<Long> ids) {
        synchronized (this) {
            ids.forEach(this::_add);
        }
    }

    private void _remove(long id) {
        int i;

        if (id <= middle_key) {
            if ((i = Arrays.binarySearch(keys, cache_offset, cache_first_index, id)) >= 0
                    || (i = Arrays.binarySearch(keys, 0, first_index, id)) >= 0) {
                set_deleted(i);
            }
        } else {
            if ((i = Arrays.binarySearch(keys, cache_bottom_index + 1, keys.length, id)) >= 0
                    || (i = Arrays.binarySearch(keys, bottom_index + 1, cache_offset, id)) >= 0) {
                set_deleted(i);
            }
        }
    }

    public void remove(long id) {
        synchronized (this) {
            _remove(id);
        }
    }

    public void remove(List<Long> ids) {
        synchronized (this) {
            ids.forEach(this::_remove);
        }
    }

    public int size(){
        return first_index + (cache_offset - bottom_index -1)
                + (cache_first_index - cache_offset) + (keys.length - cache_bottom_index - 1) - deleted_size;
    }

    public void  print(){
        System.out.println("----------");
        System.out.println("first_index:"+first_index +" bottom_index:"+bottom_index
                +" cache_offset:" + cache_offset + " cache_first_index:" +cache_first_index
                + " cache_bottom_index:" + cache_bottom_index +" length:"+ keys.length +" size:" + size());
        for ( int i = 0; i < keys.length; i++ ){
            if(i==first_index){
                System.out.print("|");
            }
            if(i==cache_offset){
                System.out.print("|");
            }
            if(i==cache_first_index){
                System.out.print("|");
            }
            if( (i < first_index) || (i > bottom_index && i < cache_offset)
                    || (i >= cache_offset && i < cache_first_index) || (i > cache_bottom_index )){
                System.out.print(keys[i]);
                if( is_deleted(i)){
                    System.out.print("X");
                }
                System.out.print(" ");
            }
        }
        System.out.println();
        System.out.println("-----------------");
    }

    public static void randomTest( int num ){
        ArrayList<Long> arrayList = new ArrayList<>();
        Sorted_long_set2 sorted_long_set2 = new Sorted_long_set2(4);

        for( int i = 0; i < num; i++ ){
            arrayList.add((long)i);
        }

        int n = 0;
        for( long a : arrayList) {
            sorted_long_set2.add(a);
            assert sorted_long_set2.contain(a);
            sorted_long_set2.add(a);
            n++;
            assert sorted_long_set2.size() == n;
            //System.out.println(n);
            //sorted_long_set2.print();
        }
        n = 0;
        for( long a : arrayList ){
            //sorted_long_set2.print();
            assert sorted_long_set2.contain(a);
            sorted_long_set2.remove(a);
            n++;
            assert sorted_long_set2.size() == arrayList.size() - n;
            assert !sorted_long_set2.contain(a);
            sorted_long_set2.remove(a);
        }

        assert sorted_long_set2.size() == 0;
        Collections.shuffle(arrayList);
        n = 0;
        for( long a : arrayList) {
            sorted_long_set2.add(a);
            //System.out.println(a);
            //sorted_long_set2.print();
            assert sorted_long_set2.contain(a);
            sorted_long_set2.add(a);
            n++;
            assert sorted_long_set2.size() == n;
        }
        Collections.shuffle(arrayList);
        n = 0;
        for( long a : arrayList ){
            assert sorted_long_set2.contain(a);
            sorted_long_set2.remove(a);
            n++;
            assert sorted_long_set2.size() == arrayList.size() - n;
            assert !sorted_long_set2.contain(a);
            sorted_long_set2.remove(a);
        }

        assert sorted_long_set2.size() == 0;
        Collections.shuffle(arrayList);
        ArrayList<Long> delList = new ArrayList<>();
        for( long a : arrayList ){
            sorted_long_set2.add(a);
        }
        Collections.shuffle(arrayList);
        for( int i = 0; i <= arrayList.size()/2; i++ ){
            sorted_long_set2.remove(arrayList.get(i));
            delList.add(arrayList.get(i));
        }
        Collections.shuffle(arrayList);
        n = 0;
        for( long a : arrayList ){
            assert (!delList.contains(a) && sorted_long_set2.contain(a))
                    || (delList.contains(a) && !sorted_long_set2.contain(a));
            sorted_long_set2.add(a);
            if(delList.contains(a)) {
                n++;
            }
            assert sorted_long_set2.contain(a);
            assert sorted_long_set2.size() == arrayList.size() - delList.size() + n;
        }
        sorted_long_set2.remove(arrayList);


        assert sorted_long_set2.size() == 0;
        delList.clear();
        Collections.shuffle(arrayList);
        n = 0;
        //arrayList.forEach(a->System.out.print(a+" "));
        //System.out.println(" begin ");
        for( long a : arrayList ){
            sorted_long_set2.add(a);
            delList.add(a);
            n++;
            //System.out.println(a);
            //sorted_long_set2.print();
            if (delList.size() > 10 ) {
                List<Long> list = delList.subList(delList.size() - 5, delList.size());
                //list.forEach(b->System.out.print(b+" "));
                //System.out.println();
                for ( long b : list ){
                    assert sorted_long_set2.contain(b);
                    sorted_long_set2.remove(b);
                    assert !sorted_long_set2.contain(b);
                    //sorted_long_set2.print();
                }
                n -= list.size();
                delList.clear();
            }
            assert sorted_long_set2.size() == n;
        }
    }

    public static void main(String[] args) {
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
            Sorted_long_set2 sorted_long_set2 = new Sorted_long_set2(4);
            for (int i = 10000000 - 1; i >= 0; i--) {
                sorted_long_set2.add(i);
            }
            System.out.println(sorted_long_set2.move_num);

            for( int i = 0; i < 10000000; i++ ){
                sorted_long_set2.remove(i);
            }
        }
        end_time = System.currentTimeMillis();
        System.out.println("Sorted_long_set2:"+(end_time - start_time) + "ms");
    }
}
