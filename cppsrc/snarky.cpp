#include <fstream>
#include <iostream>

#include <getopt.h>
#include <stdio.h>

#include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

using namespace std;
using namespace libsnark;

void generateKeys(istream& constraintStream, ostream& pkStream, ostream& vkStream) {
    r1cs_constraint_system<Fr<default_ec_pp> > cs;
    constraintStream >> cs;
    r1cs_ppzksnark_keypair<default_ec_pp> keypair = r1cs_ppzksnark_generator<default_ec_pp>(cs);
    // Generator writes out keys
    pkStream << keypair.pk;
    vkStream << keypair.vk;
}

void generateProof(istream& pkStream, istream& inpStream, istream& witStream, ostream& pfStream) {
    r1cs_ppzksnark_proving_key<default_ec_pp> pk;
    pkStream >> pk;
    r1cs_variable_assignment<Fr<default_ec_pp> > witness;
    witStream >> witness; // can we do this?
    r1cs_variable_assignment<Fr<default_ec_pp> > input;
    inpStream >> input; // deserialization?
    r1cs_ppzksnark_proof<default_ec_pp> proof = r1cs_ppzksnark_prover<default_ec_pp>(pk, input, witness);
    pfStream << proof;
}

bool verifyProof(istream& pfStream, istream& vkStream, istream& inpStream) {
    r1cs_ppzksnark_proof<default_ec_pp> proof;
    pfStream >> proof;
    r1cs_ppzksnark_verification_key<default_ec_pp> vk;
    vkStream >> vk;
    r1cs_variable_assignment<Fr<default_ec_pp> > input;
    inpStream >> input; // can we do this?
    return r1cs_ppzksnark_verifier_strong_IC<default_ec_pp>(vk, input, proof);
}

void printFileError() {
    cout << "The wrong combination of files was specified for the requested functionality.\n";
}

void maybeCloseStream(fstream & fs) {
    if (fs.is_open()) {
        fs.close();
    }
}

int main(int argc, char* const* argv) {
    // declare option stuff
    static int generatorFlag, proverFlag, verifierFlag, reserializeFlag;
    static fstream csFileStream, provingKeyFileStream, verificationKeyFileStream, proofFileStream, witnessFileStream, inputFileStream;

    static struct option long_options[] = {
        {"generateKeys", no_argument, &generatorFlag, true},
        {"prove", no_argument, &proverFlag, true},
        {"verify", no_argument, &verifierFlag, true},
        {"reserialize", no_argument, &reserializeFlag, true},
        {"csFile", required_argument, 0, 'c'},
        {"proofFile", required_argument, 0, 'q'},
        {"provingKeyFile", required_argument, 0, 'f'},
        {"verificationKeyFile", required_argument, 0, 'k'},
        {"witnessFile", required_argument, 0, 'w'},
        {"inputFile", required_argument, 0, 'i'},
        {0,0,0,0}
    };

    // Parse options and set up files
    int option_char;
    int option_index;
    while (1) {
        option_char = getopt_long(argc, argv, "gpvrq:f:k:w:i:", long_options, &option_index);
        if (option_char == -1) {
            break;
        }
        switch (option_char) {
        case 0:
            // Do nothing if we've set a flag already
            if (long_options[option_index].flag != 0)
                break;
        case 'c':
            csFileStream.open(optarg, fstream::in|fstream::out);
        case 'q':
            proofFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'f':
            provingKeyFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'k':
            verificationKeyFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'w':
            witnessFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'i':
            inputFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case '?':
            // unknown option or missing required option
            // getopt_long prints a basic usage message
            break;
        }
    }
    if (reserializeFlag) {
        // TODO
    }
    if (generatorFlag) {
        if (csFileStream.is_open() && provingKeyFileStream.is_open() && verificationKeyFileStream.is_open()) {
            generateKeys(csFileStream, provingKeyFileStream, verificationKeyFileStream);
        } else {
            printFileError();
        }
    } else if (proverFlag) {
        if (provingKeyFileStream.is_open() && inputFileStream.is_open() && witnessFileStream.is_open() && proofFileStream.is_open()) {
            generateProof(provingKeyFileStream, inputFileStream, witnessFileStream, proofFileStream);
        } else {
            printFileError();
        }
    } else if (verifierFlag) {
        if (proofFileStream.is_open() && verificationKeyFileStream.is_open() && inputFileStream.is_open()) {
            bool ans = verifyProof(proofFileStream, verificationKeyFileStream, inputFileStream);
            if (ans) {
                cout << "Verification Succeeded!\n";
            } else {
                cout << "Verification Failed!\n";
            }
        } else {
            printFileError();
        }
    }
    
    // Release resources
    maybeCloseStream(csFileStream);
    maybeCloseStream(provingKeyFileStream);
    maybeCloseStream(verificationKeyFileStream);
    maybeCloseStream(proofFileStream);
    maybeCloseStream(witnessFileStream);
    maybeCloseStream(inputFileStream);
}
