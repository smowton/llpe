//===-- LLIO.cpp ----------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"
#include "llvm/Support/FileSystem.h"

#include <openssl/sha.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define DEBUG_TYPE "llpe-misc"

using namespace llvm;

// Functions to write a summary of the files consumed in this specialisation,
// for consumption by the LLIO watch daemon (lliowd).

// Compute SHA-1 hash of Filename:

static bool getFileSha1(std::string& Filename, unsigned char* hash) {

  SHA_CTX hashctx;
  if(!SHA1_Init(&hashctx)) {

    errs() << "SHA1_Init\n";
    return false;

  }
	
  int filefd = open(Filename.c_str(), O_RDONLY);
  if(filefd == -1) {
	  
    errs() << "Cannot open " << Filename << "\n";
    return false;

  }
	
  char readbuf[4096];
  int thisread;

  while((thisread = read(filefd, readbuf, 4096)) > 0) {

    if(!SHA1_Update(&hashctx, readbuf, thisread)) {

      errs() << "SHA1_Update\n";
      return false;

    }

  }

  if(thisread == -1) {

    errs() << "Read failed for " << Filename << "\n";
    close(filefd);
    return false;

  }

  if(!SHA1_Final(hash, &hashctx)) {

    errs() << "SHA1_Final\n";
    close(filefd);
    return false;;

  }

  close(filefd);
  return true;

}

// Get modification time of filename.

static time_t getFileMtime(std::string& filename) {

  struct stat st;
  int ret = ::stat(filename.c_str(), &st);
  if(ret == -1) {

    errs() << "Failed to stat " << filename << "\n";
    return 0;

  }

  return st.st_mtime;
  
}

// Write the lliowd configuration file relating to this specialisation run. It gives the mtime and SHA-1 of each file referenced.

void LLPEAnalysisPass::writeLliowdConfig() {

  raw_ostream* Outp;
  std::unique_ptr<raw_fd_ostream> Fdp;

  if(llioConfigFile.empty()) {

    errs() << "No config file specified, writing to stdout\n";
    Outp = &outs();

  }
  else {

    std::error_code openerror;
    Fdp.reset(new raw_fd_ostream(llioConfigFile.c_str(), openerror, sys::fs::F_None));
    if(openerror) {

      errs() << "Failed to open " << llioConfigFile << ", using stdout: " << openerror.message() << "\n";
      Fdp.reset();
      Outp = &outs();

    }
    else {

      Outp = Fdp.get();

    }

  }

  raw_ostream& Out = *Outp;

  for(std::vector<std::string>::iterator it = llioDependentFiles.begin(),
	itend = llioDependentFiles.end(); it != itend; ++it) {

    SmallVector<char, 256> relPath;
    for(unsigned i = 0, ilim = it->size(); i != ilim; ++i)
      relPath.push_back((*it)[i]);

    llvm::sys::fs::make_absolute(relPath);

    StringRef printPath(relPath.data(), relPath.size());

    Out << "\t" << printPath << " " << getFileMtime(*it) << " ";

    unsigned char hash[SHA_DIGEST_LENGTH];

    if(getFileSha1(*it, hash)) {

      for(int i = 0; i < SHA_DIGEST_LENGTH; ++i) {

	if(hash[i]/16 == 0)
	  Out << '0';
	Out.write_hex(hash[i]);

      }

      Out << "\n";

    }

  }

}

