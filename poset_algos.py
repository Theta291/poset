# Poset algorithms from "Sorting and Selection in Posets" by Daskalakis et al. Currently only the mergesort is
# implemented, along with some other stuff that makes ChainMerge a usable, mutable class. Also, I have included my own
# structure, PosetGraph, which is the equivalent of a sorted linked list for posets. It has a couple benefits ChainMerge
# does not, so it may be of interest to hybridize the two structures.

# A class that implements a set of doubly linked lists.
class LinkedLists:
    def __init__(self, lists):
        self.len = 0
        self.size = 0
        self.dict = {}
        self._tops = []
        self.extend(lists)

    @property
    def tops(self):
        return self._tops

    @tops.setter
    def tops(self, new_tops):
        self.len = len(new_tops)
        self._tops = new_tops

    # Can use repeated append here, but it's slightly slower.
    def extend(self, lists):
        self.len += len(lists)
        i = self.size
        tops = []
        for a_list in lists:
            bottom = i
            for elem in a_list:
                self.dict[i] = [elem, i-1, i+1]
                i += 1
            self.dict[bottom][1] = None
            top = i-1
            self.dict[top][2] = None
            self.tops.append(top)
            tops.append(top)
        self.size = i
        return tops

    def append(self, a_list):
        self.len += 1
        i = self.size
        bottom = i
        for elem in a_list:
            self.dict[i] = [elem, i-1, i+1]
            i += 1
        self.dict[bottom][1] = None
        top = i-1
        self.dict[top][2] = None
        self.tops.append(top)
        return top
        
    def __iter__(self): return LinkedListsIterator(self)

    def pop_top(self, i):
        top = self.tops[i]
        top_node = self.dict.pop(top)
        under = top_node[1]
        if under is None:
            self.tops.pop(i)  # Gotta be careful with the time complexity of this pop.
            # Luckily, it only occurs once per peeling iteration.
            self.len -= 1
        else:
            self.dict[under][2] = None
            self.tops[i] = under
        return top_node[0]

    def copy(self):
        ret_lists = type(self)([])
        ret_lists.dict = {k: v.copy() for k, v in self.dict.items()}
        ret_lists.tops = self.tops.copy()
        ret_lists.size = self.size
        ret_lists.len = self.len
        return ret_lists

    def __len__(self): return self.len

    def link(self, *tups, new_tops=None):
        for tup in tups:
            self._raw_link(tup)
        if new_tops is None:
            self.tops = [num for num, node in self.dict.items() if node[2] is None]
        else:
            self.tops = new_tops

    def _raw_link(self, tup):
        i, j = tup
        i_next = None
        j_prev = None
        if i is not None:
            i_node = self.dict[i]
            i_next = i_node[2]
            i_node[2] = j
        if j is not None:
            j_node = self.dict[j]
            j_prev = j_node[1]
            j_node[1] = i
        if i_next is not None:
            self.dict[i_next][1] = None
        if j_prev is not None:
            self.dict[j_prev][2] = None


class LinkedListsIterator:
    def __init__(self, linked_lists):
        self.dict = linked_lists.dict
        self.tops = linked_lists.tops.copy()
        self.fetcher = self._fetch_list()

    def _fetch_list(self):
        for top in self.tops:
            num = top
            ret_list = []
            while not (num is None):
                i_node = self.dict[num]
                ret_list.append(i_node[0])
                num = i_node[1]
            ret_list.reverse()
            yield ret_list

    def __next__(self): return next(self.fetcher)


class ChainDecomp:
    def __init__(self, values, comp=None, reduce=False):
        if comp is None:
            self.comp = lambda x, y: x > y  # I know this is a little wrong, but idc.
        else:
            self.comp = comp

        self._size = len(values)
        if self._size >= 2:
            halfway = int(self._size / 2)
            first_half = values[:halfway]
            second_half = values[halfway:]
            first_decomp = ChainDecomp(first_half, self.comp)
            second_decomp = ChainDecomp(second_half, self.comp)
            self._chains = [*first_decomp._chains, *second_decomp._chains]
        else:
            self._chains = [[value] for value in values]
        self._peeling()

    @property
    def _chains(self):
        return self.__chains

    @_chains.setter
    def _chains(self, chains):
        self.__chains = chains
        self._width = len(chains)
        self._values = set()
        for chain in chains:
            self._values.update(chain)
        self._size = len(self._values)

    def _peeling(self):
        chain_links = LinkedLists(self._chains)

        # Loop while q > w
        try:
            while True:
                self._peeling_iteration(chain_links)
        
        except StopIteration:
            self._chains = list(chain_links)

    def _peeling_iteration(self, links, start_chain=0):
        chain_copies = links.copy()
        start_len = len(chain_copies)
        L = self._get_all_pairs(start_len, start_chain)
        dislodgers = {}
        pair_gen = self._find_pair(L, chain_copies)
        while len(chain_copies) == start_len:
            i, j, i_num, j_num = next(pair_gen)  # Raises StopIteration if minimum width is reached
            dislodgers[j_num] = i_num
            last_dislodged = j_num
            chain_copies.pop_top(j)
            self._replace_pairs(L, j, len(chain_copies))
        subseq = self._find_dislod_subseq(dislodgers, last_dislodged, links)
        new_tops = links.tops
        new_tops.remove(subseq[0][0])
        links.link(*subseq, new_tops=new_tops)
        return subseq

    @staticmethod
    def _get_all_pairs(num, start=0):
        L = set()  # Unfortunately this makes it a little nondeterministic,
        # but it's much better than any list or dict solution I could think of.
        for i in range(start, num):
            for j in range(i+1, num):
                L.add((i, j))
        return L

    def _find_pair(self, L, chain_copies):
        while len(L) > 0:
            i, j = L.pop()
            i_num = chain_copies.tops[i]
            j_num = chain_copies.tops[j]
            x, y = chain_copies.dict[i_num][0], chain_copies.dict[j_num][0]
            if self.comp(y, x):
                pass
            elif self.comp(x, y):
                i, j = j, i
                i_num, j_num = j_num, i_num
            else:
                continue
            
            yield i, j, i_num, j_num

    @staticmethod
    def _replace_pairs(L, i, num_chains):
        for j in range(0, i):
            L.add((j, i))
        for j in range(i+1, num_chains):
            L.add((i, j))
            
    @staticmethod
    def _find_dislod_subseq(dislodgers, last_dislodged, chain_links):
        subseq = []
        dislodged = last_dislodged
        while not (dislodged is None):
            dislodger = dislodgers[dislodged]
            subseq.append((dislodger, dislodged))
            dislodged = chain_links.dict[dislodger][2]
        subseq.reverse()
        return subseq

    @staticmethod
    def _prep_for_insert_peeling(chain_links, tops_sizes, mids_sizes):
        new_tops = []
        parent_chains = {}
        child_chains = {}
        for top, top_size, mid_size in zip(chain_links.tops, tops_sizes, mids_sizes):
            prev_top = None
            try:
                for i in range(top_size):
                    prev_top = top
                    top = chain_links.dict[top][1]
            except KeyError:
                raise ValueError(f'top_size {top_size} is greater than chain size')
            if top is not None:
                parent_chains[top] = prev_top
                mid_top_node = chain_links.dict[top]
                mid_top_node[2] = None
                new_tops.append(top)
            if prev_top is not None:
                chain_links.dict[prev_top][1] = None

            prev_top = None
            try:
                for i in range(mid_size):
                    prev_top = top
                    top = chain_links.dict[top][1]
            except KeyError:
                raise ValueError(f'top_size {top_size} + mid_size {mid_size} is greater than chain size')
            if top is not None:
                child_top_node = chain_links.dict[top]
                child_top_node[2] = None
            if prev_top is not None:
                child_chains[prev_top] = top
                chain_links.dict[prev_top][1] = None

        chain_links.tops = new_tops
        return chain_links, parent_chains, child_chains

    def _check_chains(self):
        vals = set()
        for i, chain in enumerate(self._chains):
            if len(vals.intersection(chain)):
                raise ValueError("Chains are not disjoint.")
            vals.update(chain)
            chain_offset = chain[1:]
            compares = zip(chain_offset, chain)
            if not all([self.comp(*pair) for pair in compares]):
                raise ValueError(f"self.chains[{i}] is not ascending")
        return True

    def _pop(self, chain_num, pos):
        chain = self._chains[chain_num]
        return chain.pop(pos)

    def copy(self):
        copy = type(self)([], self.comp)
        copy._width = self._width
        copy._chains = [chain.copy() for chain in self._chains]
        return copy

    def add(self, value):
        self._size += 1
        self._values.add(value)
        rets = iter(self._search_dom_sub(value))
        flag = next(rets)
        if flag:
            doms, subs, insert, pos = rets
            if insert is None:
                # Idea: keep track of which other chains an element can be inserted in, and then shuffle them around to
                # try to fit new element
                #   It can be shown that if you cannot form an antichain on length w+1 with the value and all elements
                #   to comparable to value, then there is one chain where all the elements not comparable to value are
                #   comparable to elements in other chains not comparable to value. Maybe try to insert those elements
                #   elsewhere?

                # I re-use the peeling algo on only the elements not comparable to value. If these can be peeled,
                # then that means I can create a chain where the value can be inserted. I have a proof that this is true
                # and is also the only case where value can be inserted.
                tops_sizes = [len(chain) - least_sub for chain, least_sub in zip(self._chains, subs)]
                mids_sizes = [least_sub - greatest_dom - 1 for least_sub, greatest_dom in zip(subs, doms)]
                chain_links = LinkedLists(self._chains)
                chain_links, parent_chains, child_chains = self._prep_for_insert_peeling(chain_links, tops_sizes, mids_sizes)

                try:
                    subseq = self._peeling_iteration(chain_links)
                    
                except StopIteration:
                    # Putting the new value in a new chain
                    # Testing has shown that this case takes up a lot of time, rivaling the case where the element can
                    # be inserted. This suggests that the bottleneck was the peeling iteration.
                    # (At least for my test cases.)
                    self._chains.append([value])
                    self._width += 1
                    doms.append(0)
                    subs.append(1)
                    return 3, doms, subs, self._width - 1
                
                double_parents = subseq[0][0]
                double_children = subseq[-1][1]
                unlinked_parent = parent_chains.pop(double_parents)
                unlinked_child = child_chains.pop(double_children)
                pos = chain_links.append([value])
                to_link = list(parent_chains.items())
                to_link.extend(reversed(item) for item in child_chains.items())
                to_link.append((pos, unlinked_parent))
                to_link.append((unlinked_child, pos))

                # Very heavy ops, maybe more efficient way to do these?
                chain_links.link(*to_link, new_tops=None)  # O(n)
                # Possible solution: Determine new tops
                #   Benefit: We already know what elements are at the top for all the chains that have a top not in mid.
                # Possible solution: Modify link function so that when you only link a single pair of elements it
                # detects the new top without scanning all the elements.
                self._chains = list(chain_links)  # O(n)
                # Possible solution: making self.chains a Linked_Lists instead of a list of lists.
                #   Benefits: Avoid this O(n) operation.
                #   Drawback: Have to create a fully-fledged Linked_Lists class that implements the same interface as
                #   list with the same time complexity. LinkedLists is currently not random access.
                return 2,

            else:
                self._insert(value, insert, pos, doms, subs)
                return 1, doms, subs, insert
        else:
            return 0,

    def _insert(self, value, chain_num, pos, doms, subs):
        self._chains[chain_num].insert(pos, value)

    def __contains__(self, value): return value in self._values

    def remove(self, value):
        rets = self._search_dom_sub(value)
        if rets[0]:
            raise ValueError("Value not in poset")
        else:
            self._pop(rets[1], rets[2])

    def discard(self, value):
        try:
            self.remove(value)
        except ValueError:
            pass

    def _search_dom_sub(self, value):
        doms = []
        subs = []
        insert = None
        pos = None
        # Maybe should check if value in self before doing this.
        for i, chain in enumerate(self._chains):
            greatest_dom = self._search_dominance(value, chain)
            doms.append(greatest_dom)
                
            least_sub = self._search_submission(value, chain)
            # Maybe can search only the elements greater than greatest_dom. I use a similar shortcut when search_update,
            # is true in ChainMerge, but since that updates the search bounds for every chain not yet searched it adds
            # O(w^2) operations. Searching all the ones greater than greatest_dom in this search wouldn't can give us
            # some of the benefit of that strategy without the heavy costs. A related strategy might be that the bounds
            # for the next chain are found instead of all the following chains.
            subs.append(least_sub)

            g_dom_1 = greatest_dom + 1
            if least_sub == g_dom_1:
                insert = i
                pos = least_sub
            elif least_sub == greatest_dom + 2 and chain[g_dom_1] == value:
                return 0, i, g_dom_1

        return 1, doms, subs, insert, pos

    def _search_dominance(self, value, chain, start=0, end=None):
        if end is None:
            end = len(chain)
        stepper = self._binary_stepper(end, start)
        ind_up, ind_low = next(stepper)
        while True:
            if ind_up == end:
                if self.comp(value, chain[ind_low]):
                    break
                else:
                    ind_up, ind_low = stepper.send(-1)
            elif ind_low == -1:
                if not self.comp(value, chain[ind_up]):
                    break
                else:
                    ind_up, ind_low = stepper.send(1)
            else:
                comp1 = self.comp(value, chain[ind_low])
                comp2 = not self.comp(value, chain[ind_up])
                if comp1 and comp2:
                    break
                elif comp1:
                    ind_up, ind_low = stepper.send(1)
                elif comp2:
                    ind_up, ind_low = stepper.send(-1)
                else:
                    raise IndexError(f"Search encountered error: inserting {value} into {chain}")
        stepper.close()
        return ind_low

    def _search_submission(self, value, chain, start=0, end=None):
        if end is None:
            end = len(chain)
        stepper = self._binary_stepper(end, start)
        ind_up, ind_low = next(stepper)
        while True:
            if ind_low == -1:
                if self.comp(chain[ind_up], value):
                    break
                else:
                    ind_up, ind_low = stepper.send(1)
            elif ind_up == end:
                if not self.comp(chain[ind_low], value):
                    break
                else:
                    ind_up, ind_low = stepper.send(-1)
            else:
                comp1 = self.comp(chain[ind_up], value)
                comp2 = not self.comp(chain[ind_low], value)
                if comp1 and comp2:
                    break
                elif comp1:
                    ind_up, ind_low = stepper.send(-1)
                elif comp2:
                    ind_up, ind_low = stepper.send(1)
                else:
                    raise IndexError(f"Search encountered error: inserting {value} into {chain}")
        stepper.close()
        return ind_up

    # If I ever decide to try entropysort, I can adjust this generator to account for that.
    @staticmethod
    def _binary_stepper(end, start=0):
        curr_ind = 0.5
        curr_step = 0.25
        size = (end-start)+1
        while True:
            ind_up = int(curr_ind * size) + start  # This is the line that would have to change for entropysort
            # (and maybe the line that sets the size).
            ind_low = ind_up - 1
            move = yield ind_up, ind_low
            curr_ind += move * curr_step
            curr_step *= 0.5

    def _sort_chains(self, key=len):
        permutation = sorted(range(self._width), key=lambda i: len(self._chains[i]))
        self._reorder_chains(permutation)

    def _reorder_chains(self, chain_permutation):
        def permute(a_list): return self._permute_list(a_list, chain_permutation)
        self._chains = permute(self._chains)
        return permute

    @staticmethod
    def _permute_list(a_list, permutation): return [a_list[i] for i in permutation]


class ChainMerge(ChainDecomp):
    def __init__(self, values, comp=None):
        super().__init__(values, comp)
        if self._width > 0:
            self._establish_dominance()
        else:
            self._dominance = {}
            self._submission = {}

    def _establish_dominance(self):
        width = self._width
        self._dominance = {value: [0 for i in range(width)] for value in self._values}
        self._submission = {value: [len(chain) - 1 for chain in self._chains] for value in self._values}  # Maybe can make
        # something more efficient?
        for i in range(width):
            chain1 = self._chains[i]
            for j in range(width):
                if i == j:
                    for n, v in enumerate(chain1):
                        self._dominance[v][i] = n
                        self._submission[v][i] = n + 1
                else:
                    chain2 = self._chains[j]
                    self._set_dominance(chain1, chain2, j)
                    self._set_submission(chain1, chain2, j)

    def _set_dominance(self, chain1, chain2, chain2_num):
        j = 0
        y = chain2[j]
        chain2_len = len(chain2)
        for x in chain1:
            while self.comp(x, y):
                j += 1
                try:  # Not sure if I should do this try/except instead of just check j == len(chain2)
                    y = chain2[j]
                except IndexError:
                    j = chain2_len
                    break
                    # Can break out of both loops here. Might be slightly faster.
            self._dominance[x][chain2_num] = j - 1

    def _set_submission(self, chain1, chain2, chain2_num):
        j = len(chain2)-1
        y = chain2[j]
        for x in reversed(chain1):
            while self.comp(y, x):
                j -= 1
                if j < 0:
                    j = -1
                    break
                else:
                    y = chain2[j]
            self._submission[x][chain2_num] = j + 1

    def _check_dom_sub(self):
        self._check_chains()

        for val, doms in self._dominance.items():
            for chain_num, greatest_dom in enumerate(doms):
                chain = self._chains[chain_num]
                dom_str = f"self.dominance[{val}][{chain_num}]"
                chain_str = f"self.chains[{chain_num}]"
                if greatest_dom > -1:
                    elem = chain[greatest_dom]
                    if self.comp(val, elem):
                        chain_len = len(chain)
                        if greatest_dom <= chain_len - 2:
                            next_elem = chain[greatest_dom+1]
                            if self.comp(val, next_elem):
                                raise ValueError(f"{val} dominates elem greater than {dom_str} in {chain_str}")
                        else:
                            if greatest_dom >= chain_len:
                                raise ValueError(f"{dom_str} >= len({chain_str})")
                    else:
                        if elem != val:
                            raise ValueError(f"{val} doesn't dominate {chain_str}[{dom_str}]")
                else:
                    if greatest_dom < -1:
                        raise ValueError(f"{dom_str} < -1")

        for val, subs in self._submission.items():
            for chain_num, least_sub in enumerate(subs):
                chain = self._chains[chain_num]
                sub_str = f"self.submission[{val}][{chain_num}]"
                chain_str = f"self.chains[{chain_num}]"
                chain_len = len(chain)
                if least_sub < chain_len:
                    elem = chain[least_sub]
                    if self.comp(elem, val):
                        if least_sub >= 1:
                            prev_elem = chain[least_sub-1]
                            if self.comp(prev_elem, val):
                                raise ValueError(f"{val} is dominated by elem less than {sub_str} in {chain_str}")
                        else:
                            if least_sub <= -1:
                                raise ValueError(f"{sub_str} <= -1")
                    else:
                        raise ValueError(f"{val} isn't dominated by {chain_str}[{sub_str}]")
                else:
                    if least_sub > chain_len:
                        raise ValueError(f"{sub_str} > len({chain_str})")

        return True

    def add(self, value):
        rets = iter(super().add(value))
        flag = next(rets)
        if flag:
            if flag % 2:
                doms, subs, insert = rets
                if flag == 1:
                    self._insert_helper(value, insert, doms, subs)
                elif flag == 3:
                    self._dominance[value] = []
                    self._submission[value] = []
                    for dom, sub, chain in zip(doms, subs, self._chains):
                        for i, elem in enumerate(chain):
                            elem_doms = self._dominance[elem]
                            elem_subs = self._submission[elem]
                            if i <= dom:
                                elem_subs.append(0)
                                elem_doms.append(-1)
                            elif i >= sub:
                                elem_doms.append(0)
                                elem_subs.append(1)
                            else:
                                elem_doms.append(-1)
                                elem_subs.append(1)
                    self._dominance[value] = doms
                    self._submission[value] = subs
                    self._dominance[value][insert] = 0
                    self._submission[value][insert] = 1
            elif flag == 2:
                self._establish_dominance()
                # I did all the work to avoid a full peel to remove the average case O(wn) from peeling,
                # but _establish_dominance puts that wn op back in this insert for Chain_Merge
                # Idea:
                #   Keep track of which parent chains and child chains go together. If greatest dom is in the parent
                #   chain or in the child chain but not in the highest pos, then this stays the same. Same for least sub
                #   but reversed. The only times when sub and dom need to be reestablished is when these conditions are
                #   not met, and then only part of the chain needs to be scanned. This doesn't reduce the total
                #   complexity, but it reduced the average query complexity to O(w * number of elements not comparable
                #   to value), I think.

    def _insert(self, value, chain_num, pos, doms, subs):
        super()._insert(value, chain_num, pos, doms, subs)
        self._insert_helper(value, chain_num, doms, subs)

    def _insert_helper(self, value, chain_num, doms, subs):
        self._dominance[value] = doms
        self._submission[value] = subs
        for dom, sub, chain in zip(doms, subs, self._chains):
            for i, elem in enumerate(chain):
                if i <= dom:
                    pass  # Can probably do something to avoid iterating over these, saving a little time.
                else:
                    self._submission[elem][chain_num] += 1
                    if i >= sub:
                        self._dominance[elem][chain_num] += 1

    def _pop(self, chain_num, pos):
        ret = super()._pop(chain_num, pos)
        self._dominance.pop(ret)
        self._submission.pop(ret)
        for doms in self._dominance.values():
            if doms[chain_num] >= pos:
                doms[chain_num] -= 1
        for elem, subs in self._submission.items():
            if subs[chain_num] > pos:
                subs[chain_num] -= 1

        return ret

    def _search_dom_sub(self, value, search_update=False):
        if search_update:
            # Uses the updated info from each search to optimize the new search
            # However, the updates add a w^2 factor, making it slower.
            # Performance testing has shown this to be slower than regular search, but I suspect that in a dense enough
            # poset (with a low enough width) that this will be faster. I think this applies to posets where the width
            # as a function of n grows slower than log(n).

            # Perhaps if I sort the chains from shortest to longest, then only keep track of the bounds for the next
            # chain, I can make it so that a lot of the benefit from keeping track of bounds still exists, but without
            # the w^2 cost. The ordering is because finding bounds for the largest chains removes the most searches.
            #   Preliminary testing has shown that sorting already reduces the search time for searches where
            #   search_update is True, which makes sense.
            doms = []
            subs = []
            insert = None
            pos = None
            bounds = [[0, len(chain)] for chain in self._chains]
            if search_update is True:
                def num_update(n): return self._width
            else:
                def num_update(n): return min(n + search_update, self._width)
            for (i, chain), bound in zip(enumerate(self._chains), bounds):
                greatest_dom = self._search_dominance(value, chain, *bound)
                doms.append(greatest_dom)

                # Maybe I could find some way of avoiding updating the bounds that are already the best they can be?
                # i.e. other_bound[1] == other_bound[0] + 1
                #   A little testing (n = 1000) has shown that this case is rarer than I thought (0.3% incidence).
                if greatest_dom > -1:
                    greatest_dom_doms = self._dominance[chain[greatest_dom]]
                    for j in range(i, num_update(i)):
                        other_bound = bounds[j]
                        other_bound[0] = max(greatest_dom_doms[j], other_bound[0])
                
                least_sub = self._search_submission(value, chain, *bound)
                subs.append(least_sub)

                if least_sub < len(chain):
                    least_sub_subs = self._submission[chain[least_sub]]
                    for j in range(i+1, num_update(i)):
                        other_bound = bounds[j]
                        other_bound[0] = min(least_sub_subs[j], other_bound[0])

                g_dom_1 = greatest_dom + 1
                if least_sub == g_dom_1:
                    insert = i
                    pos = least_sub
                elif least_sub == greatest_dom + 2 and chain[g_dom_1] == value:
                    return 0, i, g_dom_1

            return 1, doms, subs, insert, pos
        else:
            return super()._search_dom_sub(value)

    def _reorder_chains(self, chain_permutation):
        permute = super()._reorder_chains(chain_permutation)
        for k, v in self._dominance.items():
            self._dominance[k] = permute(v)
        for k, v in self._submission.items():
            self._submission[k] = permute(v)

    def copy(self):
        copy = super().copy()
        copy.dominance = {k: v.copy() for k, v in self._dominance.items()}
        copy.submission = {k: v.copy() for k, v in self._submission.items()}
        return copy

    def __len__(self):
        return self._size

    def __iter__(self):
        return iter(self._values)

    def _naive_reduction(self):
        while True:
            try:
                for i, chain in enumerate(self._chains):
                    for n, elem in enumerate(chain):
                        doms = self._dominance[elem]
                        subs = self._submission[elem]
                        for j, other in enumerate(self._chains):
                            if len(other) >= len(chain) and j != i:
                                dom = doms[j]
                                sub = subs[j]
                                if sub == dom + 1:
                                    self._pop(i, n)
                                    doms[i] -= 1
                                    subs[i] -= 1
                                    self._insert(elem, j, sub, doms, subs)
                                    raise StopIteration
                break
            except StopIteration:
                continue

# Graph structure for storing posets with a relationship graph.
# Reduces the number of edges in a chain length from (sum 1 to n-1) to n-1
# Essentially a doubly-linked sorted list but for posets
# Uses these properties:
# For all a, b s.t. a < b, there exists a path from b to a
# E(a, b) <-> a < b and there does not exist c s.t. a < c and c < b
class PosetGraph:
    def __init__(self, values, comp=None):
        self.least = Sentinel()
        self.greatest = Sentinel()
        if comp is None:
            comp = lambda x, y: x > y  # This is also a little wrong, but again idc
        self.comp = self._add_sentinels(self.least, self.greatest)(comp)
        self.edges = {self.least: set(), self.greatest: {self.least}}
        self.reversed_edges = {self.least: {self.greatest}, self.greatest: set()}
        self.values = set(values)
        for value in self.values:
            self.add(value)

    @staticmethod
    def _add_sentinels(least, greatest):
        def decorator(comp):
            def retfunc(x, y):
                if x is least:
                    return False
                elif x is greatest:
                    return True
                elif y is least:
                    return True
                elif y is greatest:
                    return False
                else:
                    return comp(x, y)
            return retfunc
        return decorator

    def _check_correct_reversed(self):
        if self.edges.keys() != self.reversed_edges.keys():
            raise KeyError("Edges and reversed edges have different keys.")

        for child in self.edges:
            for parent in self.edges[child]:
                if child not in self.reversed_edges[parent]:
                    raise ValueError(
                        f"There is edge from {child} to {parent} but no reversed edge from {parent} to {child}")
        return True

    def _check_edges_less(self):
        self._check_correct_reversed()

        for child in self.edges:
            for parent in self.edges[child]:
                if not self.comp(child, parent):
                    raise ValueError(f"There is edge from {child} to {parent}, but {parent} is not less than {child}")
        return True

    def _check_non_transitive(self):
        self._check_edges_less()

        # Just realized this isn't correct: What if there are two vertices between connected parent and child?
        for vertex in self.values:
            for parent in self.edges[vertex]:
                for child in self.reversed_edges[vertex]:
                    if parent in self.edges[child]:
                        return ValueError(f"Edge between {child} and {parent}, but {vertex} is in between.")
        return True

    # Folding this into a function makes it slightly slower because of the if search check
    # and because to_add is unnecessary when searching.
    def _find_neighbors(self, value, parents=True, search=True):
        if parents:
            def cmp(a, b):
                return self.comp(b, a)

            to_check = [self.least]
            edges_dict = self.reversed_edges
        else:
            def cmp(a, b):
                return self.comp(a, b)

            to_check = [self.greatest]
            edges_dict = self.edges

        neighbors = set()
        no_check = []
        while len(to_check) > 0:
            curr_v = to_check.pop()
            to_add = True
            for neighbor in edges_dict[curr_v]:
                if cmp(neighbor, value):
                    # maybe find more efficient implementation than storing no_check in list and searching it
                    if neighbor not in no_check:
                        to_check.append(neighbor)
                        no_check.append(neighbor)
                    to_add = False
            if search:
                neighbors.add(curr_v)
            elif to_add:
                neighbors.add(curr_v)

        return neighbors

    # I think this algorithm is worst case O(n) query complexity.

    # In the worst case you would add an element to the middle of a chain, which would check all the elements less than
    # the element to determine parents and greater than the element to determine children. This means that to sort a
    # poset of size n, this alg would take O(~ sum 1 to n) = O(n^2). In other words, it's an insertion sort for posets.

    # Don't really know how to do average case analysis. Would have to think of what a uniform distribution of posets
    # would be before this can be calculated.
    def add(self, value):
        parents = self._find_neighbors(value, search=False)
        children = self._find_neighbors(value, False, False)

        self.edges[value] = parents
        for parent in parents:
            self.reversed_edges[parent].add(value)

        self.reversed_edges[value] = children
        for child in children:
            self.edges[child].add(value)

        for parent in parents:
            for child in children:
                self.edges[child].discard(parent)
                self.reversed_edges[parent].discard(child)

    def _reachable(self, value, parents=True):
        if parents:
            edges_dict = self.edges
        else:
            edges_dict = self.reversed_edges

        reachable = set()
        to_check = [value]
        no_check = []
        while len(to_check) > 0:
            curr_v = to_check.pop()
            neighbors = edges_dict[curr_v]
            reachable.update(neighbors)
            for neighbor in neighbors:
                if neighbor not in no_check:
                    to_check.append(neighbor)
                    no_check.append(neighbor)

        return reachable

    # I think this is worst case O(n^2), but average case is much much better.
    # Worst case is if there are n/2 children and n/2 parents. E.g. consider
    # dominance relation over points (1, 0), (0, 1), (1, 1), (1, 2), (2, 1).
    # If you remove (1, 1), each of the n/2 children will check their n/2
    # children in the _reachable method, resulting in O((n/2)^2) = O(n^2) checks.
    # A similar construction can be made for any even n.
    def remove(self, value):
        children = self.reversed_edges[value]
        parents = self.edges[value]
        del self.edges[value]
        del self.reversed_edges[value]
        for child in children:
            self.edges[child].remove(value)
        for parent in parents:
            self.reversed_edges[parent].remove(value)

        for child in children:
            less_than = self._reachable(child)
            for parent in parents:
                if parent not in less_than:
                    self.edges[child].add(parent)
                    self.reversed_edges[parent].add(child)

    def discard(self, value):
        try:
            self.remove(value)
        except KeyError:
            pass

    # This search is worst case O(n) (If the poset is one chain and you search the max element.)
    def less_than(self, value):
        less_than = self._find_neighbors(value)
        less_than.discard(self.least)
        return less_than


class Sentinel: pass

if __name__ == '__main__':
    def point_dominance(point1, point2):
        if len(point1) == len(point2):
            return all(a > b for a, b in zip(point1, point2))
        else:
            raise IndexError("Can only compare points with same dimension")

    import random as r
    r.seed(0)

    def get_rand_point(dim): return tuple(r.random() for i in range(dim))
    def get_rand_points(dim, num): return [get_rand_point(dim) for i in range(num)]

    # import time as t
    import math as m
    rand_pts = get_rand_points(3, 100)
    # rand_pts_2 = get_rand_points(3, 100)
    merge = ChainMerge(rand_pts, point_dominance)

    def get_lens(a): return [len(chain) for chain in a._chains]
    def get_logs(a_list): return sum([m.log(n) for n in a_list])
    start_lens = get_lens(merge)
    start_logs = get_logs(start_lens)
    merge._naive_reduction()
    end_lens = get_lens(merge)
    end_logs = get_logs(end_lens)