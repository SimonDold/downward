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
    append_to_proof_log("* finalize:\n", ProofPart::INVARIANT);
    int bits = proof_log_var_count + proof_log_max_cost_bits;
    ostringstream r_budget;
    ostringstream l_budget;
    r_budget << "* varcount: " << proof_log_var_count << endl << "* max cost bits: " << proof_log_max_cost_bits << endl; 
    r_budget << "@budget_Rreif  ";
    l_budget << "@budget_Lreif  ";
    for (int i = bits - 1; i >= 0; --i) {
        r_budget << " " << (1 << i) << " b_" << i << " ";
        l_budget << " " << (1 << i) << " ~b_" << i << " ";
    }
    r_budget << " >= " << optimal_cost;
    l_budget << " >= " << (1 << bits)-optimal_cost-1;
    append_to_proof_log(r_budget.str(), ProofPart::INVARIANT);
    append_to_proof_log(l_budget.str(), ProofPart::INVARIANT);

    // ensure to define spent_geq_optimal_cost and balance_leq_0
    add_spent_geq_x_bireification_aux(optimal_cost, false, false);
    add_spent_geq_x_bireification_aux(optimal_cost, true, false);
    add_spent_geq_x_bireification_aux(0, false, true);
    add_spent_geq_x_bireification_aux(0, true, true);
    // define spent_geq_optimal_cost+1 and balance_leq_-1
    add_spent_geq_x_bireification_aux(optimal_cost+1, false, false);
    add_spent_geq_x_bireification_aux(optimal_cost+1, true, false);
    add_spent_geq_x_bireification_aux(-1, false, true);
    add_spent_geq_x_bireification_aux(-1, true, true);



    ostringstream spent_all;
    spent_all << "pol  @budget_Lreif  @balance_leq_0_Lreif +  @spent_geq_" << optimal_cost << "_Rreif + "
        << endl << "* sanity check (with rup instead of e because i dont want to devide by the correct vaule i dont bother to compute and would be to large to just cover all cases)" << endl << "rup 1 ~spent_geq_" << optimal_cost << "  1 balance_leq_0  >= 1 ; -1";
    append_to_proof_log(spent_all.str(), ProofPart::DERIVATION);

    ostringstream spent_even_more;
    spent_even_more << "pol  @budget_Lreif  @balance_leq_-1_Lreif +  @spent_geq_" << optimal_cost+1 << "_Rreif + "
        << endl << "* sanity check (with rup instead of e because i dont want to devide by the correct vaule i dont bother to compute and would be to large to just cover all cases)" << endl << "rup 1 ~spent_geq_" << optimal_cost+1 << "  1 balance_leq_-1  >= 1 ; -1";
    append_to_proof_log(spent_even_more.str(), ProofPart::DERIVATION);

    ostringstream sanity;
    sanity << "* help for sanity check" << endl;
    sanity << "pol  @balance_leq_-1_Rreif  @balance_leq_0_Lreif  + " << endl;
    sanity << "rup  1 ~balance_leq_-1  1 balance_leq_0  >= 1 ; -1" << endl;
    sanity << "pol  @spent_geq_" << optimal_cost << "_Lreif  @spent_geq_" << optimal_cost+1 << "_Rreif  + " << endl;
    sanity << "rup  1 spent_geq_" << optimal_cost << "  1 ~spent_geq_" << optimal_cost+1 << " >= 1 ; -1" << endl;
    append_to_proof_log(sanity.str(), ProofPart::DERIVATION);

    ostringstream lemmas;
    lemmas << endl << endl <<"* entry lemma balance" << endl
        << "rup  1 ~s_init  1 balance_leq_" << optimal_cost << "  1 invar  >= 1 ;" << endl
        << "* goal lemma balance" << endl
        << "rup  1 ~goal  1 balance_leq_" << 0 << "  1 ~invar  >= 1 ;" << endl
        << "* transition lemma spent" << endl
        << "rup  1 ~invar  1 ~transition  1 prime^invar  >= 1 ; " <<endl
        << "notrup  1 ~goal  1 balance_leq_" << 1 << "  1 ~invar  >= 1 ;" << endl
        << endl << endl <<"* entry lemma spent" << endl 
        << "rup  1 ~s_init  1 spent_geq_1  1 invar  >= 1 ;" << endl
        << "* goal lemma spent" << endl
        << "rup  1 ~goal  1 spent_geq_" << optimal_cost << "  1 ~invar  >= 1 ;" << endl
        << "* transition lemma spent" << endl
        << "rup  1 ~invar  1 ~transition  1 prime^invar  >= 1 ; " <<endl
        << "* sanity check: goal lemma spent" << endl
        << "notrup  1 ~goal  1 spent_geq_" << optimal_cost+1 << "  1 ~invar  >= 1 ;" << endl
        << "* sanity check: goal lemma balance" << endl
        << "notrup  1 ~goal  1 balance_leq_-1  1 ~invar  >= 1 ;" << endl
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