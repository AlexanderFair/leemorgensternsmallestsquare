#include <gmpxx.h>
#include <vector>
#include <iostream>
#include <unordered_map>
#include <algorithm>

#define num mpz_class
#define generator pair<num, num>
#define ppower pair<num, unsigned int>
using std::vector;
using std::pair;
using std::cout;
using std::endl;

bool compareGeneratorsByH(const generator& a, const generator& b) {
    // only care about the h values, ie the second
    return a.second > b.second;
}

class PrimeHandler {
    private:
    vector<num> primes;
    vector<num> eightKPlus1or7Primes;
    int lastEightKPlus1or7PrimeIndex;
    public:
    PrimeHandler(){
        primes = vector<num>();
        primes.push_back(2);
        eightKPlus1or7Primes = vector<num>();
        lastEightKPlus1or7PrimeIndex = -1;
    };

    num nthPrime(int i) {
        while (primes.size() <= i) {
            mpz_t next;
            mpz_init(next);
            mpz_set(next, primes.back().get_mpz_t());
            mpz_nextprime(next, next);
            num p = num(next);

            if (p % 8 == 1 || p % 8 == 7) {
                eightKPlus1or7Primes.push_back(p);
                lastEightKPlus1or7PrimeIndex = primes.size();
            }

            primes.push_back(p);
        }
        return primes[i];
    }

    num nth8kPlus1Or7Prime(int i) {
        int primei = lastEightKPlus1or7PrimeIndex + 1;
        while (eightKPlus1or7Primes.size() <= i) {
            nthPrime(primei);
            primei++;
        }
        return eightKPlus1or7Primes[i];
    }
};


class LValue {
    private:
    num L;
    vector<ppower> factors;
    // void combineGenerators();
    void calculateGenerators();
    void extremelyBasicGenerators();
    void calculatePregenerators();
    void pregeneratorForPrime();
    // void basicGeneratorCalculation();
    generator primitiveGenerator;
    // result should have an empty generator list beforehand!
    static void mergePrimePregenerators(LValue *pow, LValue *single, LValue *result);
    // result should have an empty generator list beforehand!
    static void mergePregenerators(LValue *a, LValue *b, LValue *result);
    
    
    public:
    static PrimeHandler primeHandler;
    num Lsquared;
    int g;
    void pregeneratorsToGenerators();
    vector<generator> generators;
    vector<generator> pregenerators;
    vector<num> squaredhs;
    LValue(vector<ppower> factors, bool generate);
    // vector<num> primes();
    // vector<generator> generators();
    num h(int index);
    num hsquare(int index);

    // cond 5: H_1^2 + H_(k-1)^2 < H_k^2 - L^2
    bool cond5(int k);

    // cond 6: H_i^2 + H_j^2 < H_k^2 ‐ L^2
    // ie sum is too small
    bool cond6(int i, int j, int k);
    // cond 7: H_i^2 + H_j^2 > H_k^2 + L^2,
    // ie sum too big
    bool cond7(int i, int j, int k);
    bool isGood(int i, int j, int k);
};

PrimeHandler LValue::primeHandler = PrimeHandler();

LValue::LValue(vector<ppower> f, bool generate = true) : factors(f) {
    this->L = 1;
    this->g = 1;
    for (ppower fp : factors) {
        mpz_t res;
        mpz_init(res);
        mpz_set(res, fp.first.get_mpz_t());;
        mpz_pow_ui(res, res, fp.second);
        L *= num(res);
        g *= 2*fp.second + 1;
    }
    this->Lsquared = L*L;
    generators = vector<generator>();
    pregenerators = vector<generator>();
    if (generate)
        this->calculateGenerators();
}

void LValue::extremelyBasicGenerators() {
    // basic calculation loop through 
    num h = L + 2;
    while (h <= 7*L) {
        num msquared = (L*L + h*h) / 2;
        num m = sqrt(msquared);

        if (msquared == m*m) {
            this->generators.push_back(generator(m, h));
        }
        h += 2;
    }
}

void LValue::calculatePregenerators(){
    // also gonna do l combination, so this should only be used for L prime
    // n (the step of the progression) is from the function 4L^2(t^3-t)/(t^2+2t-1)^2

    // TODO: If L is of the form 2*a^2-1 for some a, then we can parameterize it easily!
    // in this case taking t = a/(a-1) gives us the step of the pregenerator!
    // in particular, n = 4a(a-1)(2a-1).
    // equivalently, you can do t=(b+1)/b, and then the step is 
    // n = 4b(b+1)(2b+1), and this is actually 24 * (sum of the first b squares!) which is interesting

    // if it were really easy to do so, we could find it in the form of 2a^2 - d^2, and then parameterize it
    // by t = a/(a-d).
    // but doing that is effectively what we are already doing/looking for!

    // gen possible hs by taking 1, then multiply by all of the 8k + 1 / 8k + 7 primes under L
    // put into a heap (since we need to keep sorted order)
    // 
    // the second value in this pair is which prime that possible h was last multiplied.
    // this is so that it doesnt multiply by 7, 17, 7 which would duplicate the work of doing
    // 7, 7, 17.

    // should also clean this up if its a prime. because theres only one pregenerator, dont need this whole
    // heap tomfoolery!
    vector<pair<num, int>> possibleHs = vector<pair<num, int>>();
    vector<generator> pregens = vector<generator>();
    possibleHs.push_back(pair<num, int>(1, 0));
    int iters = 0;
    while (!possibleHs.empty()) {
        iters++;
        pair<num, int> posPair = possibleHs.back();
        num pos = posPair.first;
        possibleHs.pop_back();

        // check if it is a pregenerator
        num msquared = (L*L + pos*pos) / 2;
        num m = sqrt(msquared);

        if (msquared == m*m) {
            pregens.push_back(generator(m, pos));
            std::push_heap(pregens.begin(), pregens.end(), compareGeneratorsByH);
            pregens.push_back(generator(m, -pos));
            std::push_heap(pregens.begin(), pregens.end(), compareGeneratorsByH);
        }


        // add the next possiblities
        int primei = posPair.second;
        while (primeHandler.nth8kPlus1Or7Prime(primei) * pos < L) {
            possibleHs.push_back(pair<num, int>(primeHandler.nth8kPlus1Or7Prime(primei)*pos, primei));
            primei++;
        }
    }

    // now unpack the pregenerators into the normal generators
    cout << "pregens:\n";
    while (!pregens.empty()) {
        generator pre = pregens.front();
        std::pop_heap(pregens.begin(), pregens.end(), compareGeneratorsByH);
        pregens.pop_back();
        if (pre.second>0) cout << pre.first << ' ' << pre.second << std::endl;
        // cout << 2*pre.second + 3*pre.first << ' ' << 3*pre.second + 4*pre.first << std::endl;
        this->pregenerators.push_back(pre);
        this->generators.push_back(
            generator(
                2*pre.second + 3*pre.first,
                3*pre.second + 4*pre.first
            )
        );
    }
    // now add in the Hn = 7!
    this->generators.push_back(
        generator(
            5*L,
            7*L
        )
    );
    cout << "Num of iterations in normal gen: "<< iters << std::endl;
}

void LValue::pregeneratorForPrime() {
    // we look for solutions to L = 2m^2 - h^2
    // if L = 8k + 1, then m is odd,
    // if L = 8k + 7, then m is even
    // how do i implement that?

    // h is always odd
    // h still only has 8k+1 and 8k+7 factors
    
    // vector<pair<num, int>> possibleHs = vector<pair<num, int>>();
    // possibleHs.push_back(pair<num, int>(1, 0));
    num pos = 1;
    while (pos*pos < L) {
        /*
        pair<num, int> posPair = possibleHs.back();
        num pos = posPair.first;
        cout << pos << std::endl;
        possibleHs.pop_back();
        */

        // check if it is a pregenerator
        num msquared = (L + pos*pos) / 2;
        num m = sqrt(msquared);

        if (msquared == m*m) {
            // we now have a solution to 
            generator pregen = generator(
                2*m*m+pos*pos-2*m*pos,
                abs(2*m*m + pos*pos - 4*m*pos)
            );
            this->primitiveGenerator = pregen;
            // get the generators from the pregen
            this->pregenerators.push_back(pregen);

            break;
        }

        /*
        // add the next possiblities
        int primei = posPair.second;
        // can restrict to root L!
        while (primeHandler.nth8kPlus1Or7Prime(primei)*primeHandler.nth8kPlus1Or7Prime(primei) * pos*pos < L) {
            possibleHs.push_back(pair<num, int>(primeHandler.nth8kPlus1Or7Prime(primei)*pos, primei));
            primei++;
        }
        */
       pos += 2;
    }
}

void LValue::calculateGenerators(){
    // calculatePregenerators();
    // return;
    // if prime or prime power
    if (this->factors.size() == 1){
        // prime
        if (this->factors[0].second == 1) {
            this->pregeneratorForPrime();
            return;
        }
        // power of a prime
        vector<ppower> powFactors = vector<ppower>();
        powFactors.push_back(ppower(factors[0].first, factors[0].second - 1));
        vector<ppower> singleFactors = vector<ppower>();
        singleFactors.push_back(ppower(factors[0].first, 1));

        LValue pow = LValue(powFactors);
        LValue single = LValue(singleFactors);
        LValue::mergePrimePregenerators(&pow, &single, this);
        return;
    }
    // to combine it, get lvalues for each prime and marry them together.
    // all 7s, all 17s, all 23s, 
    // it might be possible to instead of splitting them up, just adding more 7s, 17s, etc on top. but idk.
    vector<ppower> accumulateFactors = vector<ppower>();
    accumulateFactors.push_back(factors[0]);
    LValue currentGens = LValue(accumulateFactors);

    for (int i = 1; i < factors.size() - 1; i++) {
        vector<ppower> ppowerfactors = vector<ppower>();
        ppowerfactors.push_back(factors[i]);
        accumulateFactors.push_back(factors[i]);
        LValue primePower = LValue(ppowerfactors);
        LValue res = LValue(accumulateFactors, false);
        LValue::mergePregenerators(&currentGens, &primePower, &res);
        currentGens = res;
    }
    // add the last one in
    vector<ppower> ppowerfactors = vector<ppower>();
    ppowerfactors.push_back(factors.back());
    LValue primePower = LValue(ppowerfactors);
    LValue::mergePregenerators(&currentGens, &primePower, this);    
}

void LValue::mergePrimePregenerators(LValue *pow, LValue *single, LValue *result) {
    // merge the pregenerators together, writing the pregenerators into the result's pregenerator field
    // cout << "Merging generators for " << pow->factors[0].first << '^' << pow->factors[0].second << endl;
    for (generator gen : pow->pregenerators) {
        result->pregenerators.push_back(
            generator(
                gen.first * single->L,
                gen.second * single->L
            )
        );
        // cout << gen.first * single->L << ' ' << gen.second * single->L << endl;
    }
    /*
    17^4 should have these!
    59245 6647
    63869 34391
    68561 49249
    75149 65719 - primitive 
    target: 49988
    */
    num powM = pow->primitiveGenerator.first;
    num powH = pow->primitiveGenerator.second;
    num singleM = single->primitiveGenerator.first;
    num singleH = single->primitiveGenerator.second;
    // cout << "prim for pow is " << powM << ' ' << powH << endl;
    // cout << "prim for single is " << singleM << ' ' << singleH << endl;
    // do the primitive one too
    result->primitiveGenerator = generator(
        (2*singleM*powM + singleH*powH) - (singleM*powH + singleH*powM),
        abs(
            (2*singleM*powM + singleH*powH) - 2*(singleM*powH + singleH*powM)
        )
    );
    
    int pos = -1;
    for (int i = 0 ; i < result->pregenerators.size(); i++) {
        if (result->pregenerators[i].first == result->primitiveGenerator.first
            && result->pregenerators[i].second == result->primitiveGenerator.second) 
        {
            pos = i;
            break;
        }
    }
    if (pos != -1) {
        result->primitiveGenerator = generator(
            (2*singleM*powM - singleH*powH) - abs(singleM*powH - singleH*powM),
            (2*singleM*powM - singleH*powH) - 2*abs(singleM*powH - singleH*powM)
        );
        cout << pow->factors[0].second << " Took second   (9)" << endl;
    } else {
        cout << pow->factors[0].second << " Took first (8)" << endl;
    }
    /*
    if (pow->factors[0].second % 2 == 1) {
        // going to be an even power
        // formula 8
        result->primitiveGenerator = generator(
            (2*singleM*powM + singleH*powH) - (singleM*powH + singleH*powM),
            abs(
                (2*singleM*powM + singleH*powH) - 2*(singleM*powH + singleH*powM)
            )
        );
    } else {
        // going to be an odd power
        // formula 9
        result->primitiveGenerator = generator(
            (2*singleM*powM - singleH*powH) - abs(singleM*powH - singleH*powM),
            (2*singleM*powM - singleH*powH) - 2*abs(singleM*powH - singleH*powM)
        );
    }
    */
    result->pregenerators.push_back(result->primitiveGenerator);
    // cout << "primitive: ";
    // cout << result->primitiveGenerator.first << ' ' << result->primitiveGenerator.second << endl << endl;
}

void LValue::mergePregenerators(LValue *a, LValue *b, LValue *result) {
    for (generator apre : a->pregenerators) {
        for (generator bpre : b->pregenerators) {
            // formula 8
            result->pregenerators.push_back(
                generator(
                    (2*apre.first*bpre.first + apre.second*bpre.second) - (apre.first*bpre.second + apre.second*bpre.first),
                    abs(
                        (2*apre.first*bpre.first + apre.second*bpre.second) - 2*(apre.first*bpre.second + apre.second*bpre.first)
                    )
                )
            );
            // formula 9
            result->pregenerators.push_back(
                generator(
                    (2*apre.first*bpre.first - apre.second*bpre.second) - abs(apre.first*bpre.second - apre.second*bpre.first),
                    (2*apre.first*bpre.first - apre.second*bpre.second) - 2*abs(apre.first*bpre.second - apre.second*bpre.first)
                )
            );
        }

        result->pregenerators.push_back(
            generator(
                apre.first * b->L,
                apre.second * b->L
            )
        );
    }

    // same as tail of previous loop
    for (generator bpre : b->pregenerators) {
        result->pregenerators.push_back(
            generator(
                bpre.first * a->L,
                bpre.second * a->L
            )
        );
    }
}

void LValue::pregeneratorsToGenerators() {
    for (generator pregen : pregenerators) {
        this->generators.push_back(
            generator (
                3*pregen.first-2*pregen.second,
                4*pregen.first-3*pregen.second
            )
        );
        this->generators.push_back(
            generator (
                3*pregen.first+2*pregen.second,
                4*pregen.first+3*pregen.second
            )
        );
    }
    // remember to add this one in!
    this->generators.push_back(
        generator(
            5*L,
            7*L
        )
    );
    // this will absolutely never be a bottle neck lol
    std::sort(generators.begin(), generators.end());
}

num LValue::h(int index) {
    while (this->generators.size() <= index) {
        num m = generators[generators.size() - g].first;
        num h = generators[generators.size() - g].second;
        num newh = 3*h + 4*m;
        num newm = 3*m + 2*h;
        generators.push_back(generator(newm, newh));
    }
    return generators[index].second;
}

num LValue::hsquare(int index) {
    // force the generation of all of the generators
    this->h(index);
    while (this->squaredhs.size() <= index) {
        this->squaredhs.push_back(
            generators[squaredhs.size()].second * generators[squaredhs.size()].second
        );
    }
    return squaredhs[index];
}

bool LValue::cond5(int k) {
    return this->hsquare(0) + this->hsquare(k-1) < this->hsquare(k) - this->Lsquared;
}

bool LValue::cond6(int i, int j, int k) {
    return this->hsquare(i) + this->hsquare(j) < this->hsquare(k) - this->Lsquared;
}

bool LValue::cond7(int i, int j, int k) {
    return this->hsquare(i) + this->hsquare(j) > this->hsquare(k) + this->Lsquared;
}

bool LValue::isGood(int i, int j, int k) {
    bool res = this->hsquare(i) + this->hsquare(j) == this->hsquare(k) + this->Lsquared;
    if (res) {
        cout << "OH YAAAAAA WE GOT ONE\n";
        cout << "L: " << L;
        cout << "\nLsquared: " << Lsquared << '\n';
        cout << "i: " << i;
        cout << "\nj: " << j;
        cout << "\nk: " << k;
    }
    return res;
}