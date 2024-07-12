#include <iostream>
#include <vector>
#include "generators.cpp"

using std::cout;
using std::cin;
using std::endl;

// returns true if it finds a solution with this k
// (actually it just exits)
bool checkK(LValue l, int k) {
    // if you get to a point where you cannot reject it, go to the next one generated by this, ie to k+g
    if (l.cond6(k-2, k-1, k)){
        return false;
    }
    // cout << k << std::endl;
    int i = 0;
    int j = k - 1;
    bool canReject = l.cond5(k);
    // cout << canReject << std::endl;
    while (i != j) {
        if (l.cond6(i, j, k)) {
            i++;
        } else if (l.cond7(i, j, k)) {
            j--;
        } else {
            if (l.isGood(i, j, k)) exit(0);
            // cout << "here" << std::endl;
            canReject = false;
            if (l.hsquare(i) + l.hsquare(j) < l.hsquare(k) + l.Lsquared){
                i++;
            } else {
                j--;
            }
        }
    }
    
    if (canReject){
        // cout << "rejected!" << std::endl;
        return false;
    }
    // cout << "couldn't reject, going deeper! " << k << std::endl;
    return checkK(l, k + l.g);
}

int main() {
    // cout << "Enter the bound to search to. This will search with all of the primes under";
    // cout << " that bound, at their biggest possible exponent such that its still under the bound.\n"; 
    // num bound;
    // cin >> bound;
    LValue l = LValue(vector<ppower>(), false);
    vector<ppower> factors = vector<ppower>();
    // int i = 0;
    // while (l.primeHandler.nth8kPlus1Or7Prime(i) < bound) {
    //     num prime = l.primeHandler.nth8kPlus1Or7Prime(i);
    //     int power = 1;
    //     // yes i could do a log, but eh?
    //     num exponeneted = prime;
    //     while (exponeneted*prime < bound) {
    //         exponeneted *= prime;
    //         power++;
    //     }
    //     cout << "Number will contain " << prime << " with exponent " << power << std::endl;
    //     factors.push_back(ppower(prime, power));
    //     i++;
    // }
    factors.push_back(ppower(7, 1000));
    // factors.push_back(ppower(17, 3));
    // factors.push_back(ppower(23, 2));
    // factors.push_back(ppower(31, 1));
    l = LValue(factors);
    cout << "\nIn main!\nl has " << l.g << " pregenerators"<< std::endl;
    // for ( auto g : l.pregenerators) {
    //     cout << g.first << ' ' << g.second << std::endl;
    // }
    l.pregeneratorsToGenerators();
    // cout << "\nIn main!\nl has " << l.g << " generators"<< std::endl;
    // for ( auto g : l.generators) {
    //     cout << g.first << ' ' << g.second << std::endl;
    // }
    // cond 5: H_1^2 + H_(k-1)^2 < H_k^2 - L^2

    // cond 6: H_i^2 + H_j^2 < H_k^2 ‐ L^2
    // ie sum is too small

    // cond 7: H_i^2 + H_j^2 > H_k^2 + L^2,
    // sum is too big

    // thm says that if for g consecutive values of k we have that cond (5) holds, and that 
    // for each of those k we have that for all i, j with i < j < k, one of cond 6 or 7 hold,
    // then we are done and the number is not part of a square

    // need to implement:
    // if condition 6 holds for all i, j, then can skip k+n*g for all n
    
    
    for (int k = 2; k < l.g + 2; k++){
        if (checkK(l, k)){
            exit(0);
        }
    }
    
    // int k = 2;
    // int numConsecutive = 0;
    // while (numConsecutive < l.g) {
    //     // test this k!
    //     // start with i = 1, j = k-1
    //     int i = 0;
    //     int j = k - 1;
    //     // doing this might skip a good one!!
    //     // if (!l.cond5(k)) {
    //     //     if (numConsecutive) cout << "couldn't reject! had to reset when numConsecutive was at " << numConsecutive << std::endl;
    //     //     numConsecutive = 0;
    //     //     k++;
    //     //     continue;
    //     // }

    //     // he said that cond6(k-2, k-1, k) is the most common case
    //     if (l.cond6(k-2, k-1, k)) {
    //         // then cond6 is true for all i, k
    //         numConsecutive++;
    //         k++;
    //         continue;
    //     }

    //     // now do the walk up / down
    //     // if sum to small, (6), then incrememnt i.
    //     // if sum too big (7), then decrement j.
    //     // can we speed this up?
    //     // if i too small, skip it to center?
    //     // FUTURE OPTIMIZATION: if sum is too small, bin search for largest i where its still
    //     // too small, then go one above that. if its too large, do same but looking for smallest j where sum
    //     // is still too big, then go one beneath that
    //     while (i != j) {
    //         if (l.cond6(i, j, k)) {
    //             i++;
    //             continue;
    //         } else if (l.cond7(i, j, k)) {
    //             j--;
    //             continue;
    //         } else {
    //             // neither is true, cannot reject this k
    //             // hope tho lol
    //             l.isGood(i, j, k);
    //             break;
    //         }
    //     }

    //     if (i != j) {
    //         // we broke out of the loop!! this k cannot be rejected :(
    //         if (numConsecutive) cout << "couldn't reject! had to reset when numConsecutive was at " << numConsecutive << std::endl;
    //         numConsecutive = 0;
    //         k++;
    //         continue;
    //     }

    //     // otherwise we can reject this and move on!
    //     numConsecutive++;
    //     k++;
    // }
    cout << "This L cannot be part of a magic square!\n";
    // cout << "Checked " << k << " progressions\n";
}