
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/stat.h>
#include <sys/inotify.h>

#include <openssl/sha.h>

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>

#include <iostream>
#include <vector>
#include <sstream>
#include <fstream>

using namespace std;

#define UNIX_PATH_MAX 108

// watch_fd is set to -1 if files are already non-matching.
struct spec_program {

  std::string binary_name;
  int watch_fd;

};

std::vector<struct spec_program> progs;

static struct spec_program* findprog(const char* name) {

  std::string names(name);

  for(std::vector<struct spec_program>::iterator it = progs.begin(), itend = progs.end(); it != itend; ++it)
    if(it->binary_name == names)
      return &*it;
  
  return 0;

}

static int firstnonws(std::string& s) {

  for(int i = 0, ilim = s.size(); i != ilim; ++i) {

    if(!isspace(s[i]))
      return i;

  }

  return s.size();

}

static void mark_failed(struct spec_program& prog) {

  close(prog.watch_fd);
  prog.watch_fd = -1;

}

static void parse_config(const char* confname) {

  ifstream ifs(confname);
  while(!ifs.eof()) {

    std::string line;
    getline(ifs, line);

    while(line.size() && isspace(line.back()))
      line.erase(line.size() - 1);

    int wsoff = firstnonws(line);
    if(wsoff == line.size()) {

      continue;

    }
    else if(wsoff == 0) {
      
      // Start new program
      progs.push_back(spec_program());
      progs.back().binary_name = line;

      int new_watch = inotify_init();

      if(new_watch == -1) {

	cerr << "Inotify open failed\n";
	exit(1);

      }

      progs.back().watch_fd = new_watch;

      cout << "Adding program " << progs.back().binary_name << "\n";

    }
    else {

      if(progs.empty()) {

	cerr << "Indented line at start of config\n";
	exit(1);

      }

      // Already failed?
      if(progs.back().watch_fd == -1)
	continue;

      // New file
      std::string fline(line, wsoff);

      // Last two fields: expected unix time (decimal), expected sha256 hash (hex)
      unsigned hashstart = fline.find_last_of(" ");
      if(hashstart == std::string::npos || hashstart == 0) {

	cerr << "Bad line " << fline << "\n";
	exit(1);

      }

      unsigned timestart = fline.find_last_of(" ", hashstart - 1);
      if(timestart == std::string::npos || timestart == 0) {

	cerr << "Bad line " << fline << "\n";
	exit(1);

      }
      
      std::string fname(fline, 0, timestart);

      // Add an inotify watch *before* verifying file, to avoid race.
      if(inotify_add_watch(progs.back().watch_fd, fname.c_str(), IN_ATTRIB | IN_DELETE_SELF | IN_MODIFY) == -1) {

	cerr << "Failed adding watch: " << fname << "\n";
	mark_failed(progs.back());
	continue;

      }

      // First of all: file exists?
      struct stat filestat;
      if(stat(fname.c_str(), &filestat) == -1) {

	cerr << fname << ": not found\n";
	mark_failed(progs.back());
	continue;

      }

      std::string timestr(fline, timestart + 1, hashstart - timestart);

      // mtimes match?
      {
	std::istringstream iss(timestr);
	time_t expected_time;
	iss >> expected_time;

	if(expected_time != filestat.st_mtime) {

	  cerr << fname << ": bad mtime (expected " << expected_time << ", got " << filestat.st_mtime << "\n";
	  mark_failed(progs.back());
	  continue;

	}
      }

      // Get hash of the real file:

      unsigned char realhash[SHA_DIGEST_LENGTH];
      {
	SHA_CTX hashctx;
	if(!SHA1_Init(&hashctx)) {

	  cerr << "SHA1_Init\n";
	  exit(1);

	}
	
	int filefd = open(fname.c_str(), O_RDONLY);
	if(filefd == -1) {
	  
	  cerr << "Cannot open " << fname << "\n";
	  mark_failed(progs.back());
	  continue;

	}
	
	char readbuf[4096];
	int thisread;

	while((thisread = read(filefd, readbuf, 4096)) > 0) {

 	  if(!SHA1_Update(&hashctx, readbuf, thisread)) {

	    cerr << "SHA1_Update\n";
	    exit(1);

	  }

	}

	if(thisread == -1) {

	  cerr << "Read failed for " << fname << "\n";
	  mark_failed(progs.back());
	  close(filefd);
	  continue;

	}

	if(!SHA1_Final(realhash, &hashctx)) {

	  cerr << "SHA1_Final\n";
	  exit(1);

	}

	close(filefd);

      }

      // Parse hash given in config:
      unsigned char expectedhash[SHA_DIGEST_LENGTH];
      std::string hashstr(fline, hashstart + 1);

      if(hashstr.size() != SHA_DIGEST_LENGTH * 2) {

	cerr << hashstr << " wrong length (expected " << (SHA_DIGEST_LENGTH * 2) << ", got " << hashstr.size() << ")\n";
	exit(1);

      }

      {
	istringstream iss(hashstr);
	for(int i = 0; i < SHA_DIGEST_LENGTH; ++i) {

	  char hexchars[3];
	  iss.get(hexchars, 3);
	  hexchars[2] = '\0';
	  expectedhash[i] = (char)strtol(hexchars, 0, 16);

	}
      }

      if(memcmp(expectedhash, realhash, SHA_DIGEST_LENGTH) != 0) {

	cerr << "Hash bad match: expected: " << hashstr << ", got: ";
	for(int i = 0; i < SHA_DIGEST_LENGTH; ++i) {

	  cerr << std::hex << (unsigned int)realhash[i];

	}
	cerr << "\n";

	mark_failed(progs.back());
	continue;

      }

      cout << "Verified " << fname << "\n";

    }

  }

}

static int createlistensock() {

  int listenfd = socket(AF_UNIX, SOCK_STREAM, 0);
  if(listenfd == -1) {

    fprintf(stderr, "Socket\n");
    exit(1);

  }

  struct sockaddr_un bindaddr;
  bindaddr.sun_family = AF_UNIX;
  
  const char* homedir = getenv("HOME");
  if(!homedir) {

    fprintf(stderr, "HOME not set\n");
    exit(1);

  }

  if(snprintf(bindaddr.sun_path, UNIX_PATH_MAX, "%s/.lliowd-socket", homedir) >= UNIX_PATH_MAX) {

    fprintf(stderr, "Socket path too long\n");
    exit(1);

  }

  unlink(bindaddr.sun_path);

  if(bind(listenfd, (struct sockaddr*)&bindaddr, sizeof(struct sockaddr_un)) == -1) {

    fprintf(stderr, "Bind failed\n");
    exit(1);

  }

  if(listen(listenfd, 5) == -1) {

    fprintf(stderr, "Listen failed\n");
    exit(1);

  }

  return listenfd;

}

int main(int argc, char** argv) {

  if(argc < 2) {
    fprintf(stderr, "Usage: lliowd config_file\n");
    exit(1);
  }

  parse_config(argv[1]);

  int listenfd = createlistensock();

  while(1) {

    struct sockaddr_un otherend;
    socklen_t otherendlen;
    int connfd = accept(listenfd, (struct sockaddr*)&otherend, &otherendlen);

    if(connfd == -1) {
      fprintf(stderr, "Accept failed\n");
      continue;
    }

    struct ucred otherendcreds;
    socklen_t otherendcredslen = sizeof(struct ucred);
    if(getsockopt(connfd, SOL_SOCKET, SO_PEERCRED, &otherendcreds, &otherendcredslen) == -1) {

      fprintf(stderr, "getsockopt failed\n");
      close(connfd);
      continue;

    }

    char pathbuf[128];
    sprintf(pathbuf, "/proc/%d/exe", otherendcreds.pid);

    char exebuf[4096];
    ssize_t rlret = readlink(pathbuf, exebuf, 4096);
    if(rlret < 0 || rlret == 4096) {

      cerr << "Path name too long for " << pathbuf << "\n";
      close(connfd);
      continue;

    }

    exebuf[rlret] = '\0';

    struct spec_program* prog = findprog(exebuf);
    if(!prog) {

      cerr << "No such program " << exebuf << "\n";
      close(connfd);
      continue;

    }

    if(prog->watch_fd == -1) {

      // Couldn't verify this program's files
      if(send(connfd, "\0", 1, MSG_NOSIGNAL) == -1)
	cerr << "Write failed\n";

    }
    else {

      // The program's files were good at startup, and hopefully remain so! Send the inotify handle:
      struct msghdr hdr;
      struct iovec data;

      char cmsgbuf[CMSG_SPACE(sizeof(int))];

      char dummy = '\x01';
      data.iov_base = &dummy;
      data.iov_len = sizeof(dummy);

      memset(&hdr, 0, sizeof(hdr));
      hdr.msg_name = NULL;
      hdr.msg_namelen = 0;
      hdr.msg_iov = &data;
      hdr.msg_iovlen = 1;
      hdr.msg_flags = 0;

      hdr.msg_control = cmsgbuf;
      hdr.msg_controllen = CMSG_LEN(sizeof(int));

      struct cmsghdr* cmsg = CMSG_FIRSTHDR(&hdr);
      cmsg->cmsg_len   = CMSG_LEN(sizeof(int));
      cmsg->cmsg_level = SOL_SOCKET;
      cmsg->cmsg_type  = SCM_RIGHTS;

      *(int*)CMSG_DATA(cmsg) = prog->watch_fd;

      int n = sendmsg(connfd, &hdr, MSG_NOSIGNAL);
      if(n == -1)
	cerr << "sendmsg failed\n";

    }

    close(connfd);

  }

}
