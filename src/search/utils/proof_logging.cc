#include "proof_logging.h"

#include <cassert>
#include <fstream>
#include <iostream>
#include <regex>
#include <string>

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

void ProofLog::append_comment_to_proof_log(const std::string& comment) {
    append_to_proof_log("*"+comment, ProofPart::REIFICATION);
    append_to_proof_log("*"+comment, ProofPart::DERIVATION);
}

void ProofLog::append_to_proof_file(const string &line, const string &file_name)
{
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << line;
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

void set_vector_sum(vector<string> vectors, int x, string comment="set_vector_sum") {
    ProofLog::append_to_proof_log("*"+comment, ProofPart::REIFICATION);

    assert(x >= 0);
    int bits = ProofLog::get_proof_log_bits();
    int maxint = (1 << bits) - 1;
        ostringstream r_reif, r_witness;
        ostringstream l_reif, l_witness;
            r_reif << " red ";
            l_reif << "            red ";
        for (string vector : vectors){
            bool negative = vector[0] == '-';
            string vec_name = (negative ? vector.substr(1,vector.length()) : vector);
            if (negative){
                x += maxint;
            }
            assert(vec_name.size()>0);
            for (int i = 0; i < bits; ++i) {
                r_reif << " " << (1 << i) << " " << (negative ? "~" : " ") << vec_name << "_" << i << " ";
                r_witness << " " << vec_name << "_" << i << " -> " << (negative ? "0" : "1") << " "; 
                l_reif << " " << (1 << i) << " " << (negative ? " " : "~") << vec_name << "_" << i << " ";  
                l_witness << " " << vec_name << "_" << i << " -> " << (negative ? "1" : "0") << " ";
            }
        }
        assert(x >= 0);
        int A = x;
        int M = (vectors.size()*maxint);
        r_reif << " >= " << x << " " ;
        l_reif << " >= " << M-A+1 << " " ;
        
        ProofLog::append_to_proof_log("* A:" + to_string(A) + "M:" + to_string(M), ProofPart::REIFICATION);

        ProofLog::append_to_proof_log(r_reif.str() , ProofPart::REIFICATION);
        ProofLog::append_to_proof_log(l_reif.str() , ProofPart::REIFICATION);

}

void bireif_vector_sum(string reif_var, vector<string> vectors, int bound, string comment="bireif_vector_sum") {
    ProofLog::append_to_proof_log("*"+comment, ProofPart::REIFICATION);

        int bits = ProofLog::get_proof_log_bits();
        int maxint = (1 << bits) - 1;
        ostringstream r_reif;
        ostringstream l_reif;
        assert(reif_var.size() > 0);
        r_reif << "@" << reif_var << "_Rreif " << " red ";
        l_reif << "@" << reif_var << "_Lreif " << " red ";
        for (string vector : vectors){
            bool negative = vector[0] == '-';
            string vec_name_aux = (negative ? vector.substr(1,vector.length()) : vector);
            bool is_dynamic = vec_name_aux.back() == ':' || vec_name_aux.back() == '.';
            string postfix = (is_dynamic ? vec_name_aux.substr(vec_name_aux.length()-1,vec_name_aux.length()) : "");
            string vec_name = (is_dynamic ? vec_name_aux.substr(0,vec_name_aux.length()-1) : vec_name_aux);
            if (negative){
                assert(bound+maxint >= bound);
                bound += maxint;
            }
            assert(vec_name.size()>0);
            for (int i = 0; i < bits; ++i) {
                r_reif << " " << (1 << i) << " " << (negative ? "~" : " ") << vec_name << "_" << i << postfix << " ";  
                l_reif << " " << (1 << i) << " " << (negative ? " " : "~") << vec_name << "_" << i << postfix << " ";  
            }
            ProofLog::append_to_proof_log("* renaming: " + vector + "->" + vec_name + " and postfix: '" + postfix + "' ", ProofPart::REIFICATION);
        }
        int A = bound;
        int M = (vectors.size()*maxint);
        //r_reif << " >= " << x << " " ;
        //l_reif << " >= " << M-A+1 << " " ;
        
        ProofLog::append_to_proof_log("* A:" + to_string(A) + "M:" + to_string(M), ProofPart::REIFICATION);

        r_reif <<   A   << " ~" << reif_var << " >= " <<   A   << " ; " << reif_var << " -> 0 ";
        l_reif << M-A+1 << "  " << reif_var << " >= " << M-A+1 << " ; " << reif_var << " -> 1 ";

        ProofLog::append_to_proof_log(r_reif.str() , ProofPart::REIFICATION);
        ProofLog::append_to_proof_log(l_reif.str() , ProofPart::REIFICATION);
}

string format(string var) {
    return (var[0] == '~' ? var : " " + var);
}

string negate(string var) {
    return (var[0] == '~' ? var.substr(1,var.length()) : "~" + var);
}





void bireif_flat_formula(string reif_var, vector<string> elements, bool is_disjunction, string comment="bireif_formla") {
    ProofLog::append_to_proof_log("*"+comment, ProofPart::REIFICATION);
    ostringstream r_reif, l_reif;
    assert(reif_var.size() > 0);
    r_reif << "@" << reif_var << "_Rreif " << " red ";
    l_reif << "@" << reif_var << "_Lreif " << " red ";
    for (string element : elements) {
        r_reif << " 1 " << format(       element )         << " ";
        l_reif << " 1 " << format(negate(element)) << " ";
    }
    int A = elements.size();
    r_reif << " " << (is_disjunction ? 1 : A) << " ~" << reif_var << " >= " << (is_disjunction ? 1 : A) << " ; " << reif_var << " -> 0 ";
    l_reif << " " << (is_disjunction ? A : 1) << "  " << reif_var << " >= " << (is_disjunction ? A : 1) << " ; " << reif_var << " -> 1 ";
    ProofLog::append_to_proof_log(r_reif.str() , ProofPart::REIFICATION);
    ProofLog::append_to_proof_log(l_reif.str() , ProofPart::REIFICATION);
}

void ProofLog::bireif_conjunction(string reif_var, vector<string> conjuncts, string comment="bireif_conjunction") {
    bireif_flat_formula(reif_var, conjuncts, false, comment);
}

void ProofLog::bireif_disjunction(string reif_var, vector<string> disjuncts, string comment="bireif_disjunction") {
    bireif_flat_formula(reif_var, disjuncts, true, comment);
}

void append_file_to_proof_log(string file_2, ProofPart proof_part){
    string file_1;
    switch (proof_part)
    {
    case ProofPart::REIFICATION:
        {
            file_1= "reifications.prooflog";
            break;
        }
    case ProofPart::DERIVATION:
        {
            file_1 = "derivations.prooflog";
            break;
        }
    case ProofPart::INVARIANT:
        {
            file_1 = "invariant.prooflog"; 
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

    std::ifstream in(file_2);
    std::ofstream out(file_1, std::ios_base::out | std::ios_base::app);

    for (std::string str; std::getline(in, str); )
    {
        out << "\n\n***** APPEND FILE TO PROOF LOG\n\n" << str << endl << endl;
    }
}

void ProofLog::append_files_to_proof_log(std::vector<std::string> files, ProofPart proof_part){
    for (string file : files) {
        append_file_to_proof_log(file, proof_part);
    }
}

void add_spent_geq_x_bireification_aux(const int x, bool is_prime, bool balance){
    string e = (is_prime ? "e:" : "e.");
    ostringstream reif_var;
    reif_var << (balance ? "balance_geq_" : "spent_geq_") << x << (is_prime ? ":" : ".");
    int bits = ProofLog::get_proof_log_bits();
    int maxint = (1 << bits) -1;
    assert(x<maxint);
    bireif_vector_sum(reif_var.str(), (balance ? vector<string>{"b", "-"+e} : vector<string>{e}), x, "add_spent_geq_x_bireif_aux");

    // bireif of inverse statement  b_leq_2 iff ~b_geq_3    sp_geq_2 iff ~sp_leq_1
    ostringstream reif_var2, conjunct;
    reif_var2 << (balance ? "balance_leq_" : "spend_leq_") << x - 1 << (is_prime ? ":" : ".");
    conjunct << "~" << (balance ? "balance_geq_" : "spend_geq_") << x << (is_prime ? ":" : ".");
    ProofLog::bireif_conjunction(reif_var2.str(), vector<string>({conjunct.str()}));

}

void ProofLog::bireif_balance_leq(int x) {
    add_spent_geq_x_bireification_aux(x+1, false, true);
    add_spent_geq_x_bireification_aux(x+1, true, true);

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

    // TODOprooflogging remove this:
        append_to_proof_log("* ensure non empty REIF file", ProofPart::REIFICATION);

    append_to_proof_log("* finalize:\n", ProofPart::INVARIANT);
    int bits = get_proof_log_bits();
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
    spent_all << "pol  @budget_Lreif  @balance_leq_0._Lreif " << (1 << get_proof_log_bits()) << " * +  @spent_geq_" << optimal_cost << "._Rreif + @balance_geq_1._Rreif +"
        << endl << "* sanity check (with rup instead of e because i dont want to devide by the correct vaule i dont bother to compute and would be to large to just cover all cases)" << endl 
        << "rup 1 ~spent_geq_" << optimal_cost << ".  1 balance_leq_0.  >= 1 ; -1";
    append_to_proof_log(spent_all.str(), ProofPart::REIFICATION); //TODOprooflogging this should belong at the start of derivations

    ostringstream spent_even_more;
    spent_even_more << "pol  @budget_Lreif  @balance_leq_-1._Lreif " << (1 << get_proof_log_bits()) << " * +  @spent_geq_" << optimal_cost+1 << "._Rreif + @balance_geq_0._Rreif +"
        << endl << "* sanity check (with rup instead of e because i dont want to devide by the correct vaule i dont bother to compute and would be to large to just cover all cases)" << endl 
        << "rup 1 ~spent_geq_" << optimal_cost+1 << ".  1 balance_leq_-1.  >= 1 ; -1";
    append_to_proof_log(spent_even_more.str(), ProofPart::REIFICATION); //TODOprooflogging this should belong at the start of derivations

    ostringstream sanity;
    sanity << "* help for sanity check" << endl;
    sanity << "pol  @balance_leq_-1._Rreif " << (1 << get_proof_log_bits()) << " *  @balance_leq_0._Lreif " << (1 << get_proof_log_bits()) << " *  + @balance_geq_0._Lreif @balance_geq_1._Rreif + +" << endl;
    sanity << "rup  1 ~balance_leq_-1.  1 balance_leq_0.  >= 1 ; -1" << endl;
    sanity << "pol  @spent_geq_" << optimal_cost << "._Lreif  @spent_geq_" << optimal_cost+1 << "._Rreif  + " << endl;
    sanity << "rup  1 spent_geq_" << optimal_cost << ".  1 ~spent_geq_" << optimal_cost+1 << ". >= 1 ; -1" << endl;
    append_to_proof_log(sanity.str(), ProofPart::REIFICATION); //TODOprooflogging this should belong at the start of derivations

    ostringstream lemmas;
    lemmas << endl << endl <<"* entry lemma balance" << endl
        << "@lem3  rup  1 ~s_init.  1 balance_leq_" << optimal_cost << ".  1 invar.  >= 1 ;" << endl
        << "* goal lemma balance" << endl
        << "@lem4  rup  1 ~goal.  1 balance_leq_" << 0 << ".  1 ~invar.  >= 1 ;" << endl
        << "* transition lemma balance" << endl
        << "@lem7  rup  1 ~invar.  1 ~transition  1 invar:  >= 1 ; " <<endl
        << endl << endl <<"* entry lemma spent" << endl 
        << "rup  1 ~s_init.  1 spent_geq_1.  1 invar.  >= 1 ;" << endl
        << "* goal lemma spent" << endl
        << "rup  1 ~goal.  1 spent_geq_" << optimal_cost << ".  1 ~invar.  >= 1 ;" << endl
        << "* transition lemma spent" << endl
        << "rup  1 ~invar.  1 ~transition  1 invar:  >= 1 ; " <<endl
        << "* sanity check: goal lemma spent" << endl
        << "notrup  >= 1 ;" << endl
        << "notrup  1 ~goal.  1 spent_geq_" << optimal_cost+1 << ".  1 ~invar.  >= 1 ;" << endl
        << "* sanity check: goal lemma balance" << endl
        << "notrup  >= 1 ;" << endl
        << "notrup  1 ~goal.  1 balance_leq_-1.  1 ~invar.  >= 1 ;" << endl
        << "output NONE" << endl
        << "conclusion NONE" << endl
        << "end pseudo-Boolean proof" << endl;
    append_to_proof_log(lemmas.str(), ProofPart::DERIVATION);
}

int MAX_BIT_BOUNDARY = 30;

int ProofLog::get_proof_log_maxint() {
    return (1 << get_proof_log_bits())-1;
}


int ProofLog::get_proof_log_bits() {
    // TODOprooflogging make this pivate, others should ask for maxint directly.
    return std::min(1+proof_log_max_cost_bits+proof_log_var_count, MAX_BIT_BOUNDARY);
// TODOprooflogging expreimental added +1 ... there might be some weirdness when this is exactly 2**x (+-1)  ? :( ?

    // here we will need more bits once we talk about infinity
    // it would be nice to not do this but it would require arbitrary size integer operations
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
