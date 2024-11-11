#include "proof_logging.h"

#include <fstream>
#include <iostream>
#include <sstream>

using namespace std;

namespace utils {
void appendLineToFile(string filename, string line)
// https://stackoverflow.com/a/39462191/27389055
{
    std::ofstream file;
    //can't enable exception now because of gcc bug that raises ios_base::failure with useless message
    //file.exceptions(file.exceptions() | std::ios::failbit);
    file.open(filename, std::ios::out | std::ios::app);
    if (file.fail())
        cerr << "Failed to proof_log file: " << filename << endl;

    //make sure write fails with exception if something is wrong
    file.exceptions(file.exceptions() | std::ios::failbit | std::ifstream::badbit);

    file << line << std::endl;
}


    void add_state_reification(StateID id, State s){

        

        s.unpack();
        
        ostringstream line;

        line << "R-reification r" << id << ": ~r" << id;

        auto x = s.get_unpacked_values();
        for (unsigned int i = 0; i < x.size(); ++i) {
            line << " + v" << i << "_"<< x[i];
        }
        line << " >= " << x.size() << ";";
        string line_string = line.str();


        utils::appendLineToFile("proof_log", line_string);
    }
}