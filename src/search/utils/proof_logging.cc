#include "proof_logging.h"

#include <cassert>
#include <fstream>
#include <iostream>
#include <regex>

using namespace std;


int proof_log_var_count;
int proof_log_max_cost_bits;

namespace utils {

// TODOprooflog where should this live?
int ceil_log_2(int val) { // https://stackoverflow.com/a/994647/27389055
    assert(val > 0); // Invalid input
    val = val + val; // rounding up
    if (val == 1) return 0;
    unsigned int ret = 0;
    while (val > 1) {
        val >>= 1;
        ret++;
    }
    return ret;
}

void ProofLog::append_to_proof_log(const string &line, ProofPart proof_part)
{
    string file_name;
    switch (proof_part)
    {
    case ProofPart::REIFICATION:
        {
            file_name = "reifications.prooflog";
            break;
        }
    case ProofPart::DERIVATION:
        {
            file_name = "derivations.prooflog";
            break;
        }
    case ProofPart::INVARIANT:
        {
            file_name = "invariant.prooflog"; 
            /*
                it is not truly THE invariant but all needed (and some not needed) reifications that build the invariant.
                The invariant is in the file invarinat_right.prooflog and invariant_left.prooflog
            */
            break;
        }
    default:
        cerr << "Error: Not clear where to add." << endl;
        break;
    }

    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << line << endl;
    file.close();
}

void ProofLog::append_to_invariant_right(const string& summand) {
    string file_name = "invariant_right.prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << summand;
    file.close();
}

// TODOprooflog remove 4fold code duplication 

void ProofLog::append_to_invariant_left(const string& summand) {
    string file_name = "invariant_left.prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << summand;
    file.close();
}

void ProofLog::append_to_invariant_prime_right(const string& summand) {
    string file_name = "invariant_prime_right.prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << summand;
    file.close();
}

void ProofLog::append_to_invariant_prime_left(const string& summand) {
    string file_name = "invariant_prime_left.prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << summand;
    file.close();
}

void add_spent_geq_x_bireification_aux(const int x, bool is_prime, bool balance){
    int bits = proof_log_var_count + proof_log_max_cost_bits;
    // here we will need more bits once we talk about infinity
    int maxint = 1 << bits;
    ostringstream r_prime;
    ostringstream l_prime;
    r_prime << "@" << (is_prime ? "prime^" : "") << (balance ? "balance_leq_" : "spent_geq_") << x << "_Rreif ";
    l_prime << "@" << (is_prime ? "prime^" : "") << (balance ? "balance_leq_" : "spent_geq_") << x << "_Lreif ";
    for (int i = bits - 1; i >= 0; --i) {
        r_prime << " " << (1 << i) << " " << (is_prime ? "prime^" : "") << "e_" << i << " ";
        l_prime << " " << (1 << i) << " ~" << (is_prime ? "prime^" : "") << "e_" << i << " ";
        if (balance) {
            r_prime << " " << (1 << i) << " ~b_" << i << " ";
            l_prime << " " << (1 << i) << " b_" << i << " ";
        }

    }
    if (balance) {
        r_prime << 2 * maxint - (maxint + x) - 1 << " ~" << (is_prime ? "prime^" : "") << "balance_leq_" << x << "  >= " << 2 * maxint - (maxint + x) - 1;
        l_prime << (maxint + x) << " " << (is_prime ? "prime^" : "") << "balance_leq_" << x << "  >= " << maxint + x;
    } else {
        r_prime << x << " ~" << (is_prime ? "prime^" : "") << "spent_geq_" << x << "  >= " << x;
        l_prime << ((1 << bits) - x) << " " << (is_prime ? "prime^" : "") << "spent_geq_" << x << "  >= " << ((1 << bits) - x);
    }
    ProofLog::append_to_proof_log(r_prime.str(), ProofPart::INVARIANT);
    ProofLog::append_to_proof_log(l_prime.str(), ProofPart::INVARIANT);
}

void ProofLog::add_spent_geq_x_bireification(const int x){
    add_spent_geq_x_bireification_aux(x, false, false);
    add_spent_geq_x_bireification_aux(x, true, false);
}

void ProofLog::add_balance_leq_x_bireification(const int x){
    add_spent_geq_x_bireification_aux(x, false, true);
    add_spent_geq_x_bireification_aux(x, true, true);
}

void ProofLog::finalize_lemmas(int optimal_cost) {
    ostringstream lemmas;
    lemmas << endl << endl <<"* entry lemmas" << endl
        << "rup  1 ~s_init  1 spent_geq_1  1 invar  >= 1 ;" << endl
        << "* goal lemma" << endl
        << "rup  1 ~goal  1 spent_geq_" << optimal_cost << "  1 ~invar  >= 1 ;" << endl
        << "* transition lemma" << endl
        << "rup  1 ~invar  1 ~transition  1 prime^invar  >= 1 ; " <<endl
        << "* FAKE goal lemma" << endl
        << "rup  1 ~goal  1 spent_geq_" << optimal_cost+1 << "  1 ~invar  >= 1 ;" << endl
        << "* FAKE goal lemma" << endl
        << "rup  1 ~goal  1 spent_geq_" << optimal_cost-1 << "  1 ~invar  >= 1 ;" << endl
        << "output NONE" << endl 
        << "conclusion NONE" << endl
        << "end pseudo-Boolean proof" << endl;
    append_to_proof_log(lemmas.str(), ProofPart::DERIVATION);
}

// WARNING: this function has to be syncronized with same named one in the python part.
string ProofLog::strips_name_to_veripb_name(const string& strips_name) {
    regex pattern("[a-zA-Z0-9\\[\\]\\{\\^\\-]");
    string veripb_name;
    for (char c : strips_name) {
        if (! regex_search(string(1, c), pattern)) {
            //veripb_name += "[ASCII" + to_string(static_cast<int>(c)) + "]";
            veripb_name += "_";
        } else {
            veripb_name += c;
        }
    }
    
    return veripb_name;
}
}