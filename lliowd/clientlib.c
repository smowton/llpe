
#include <lliowd.h>

#include <errno.h>

#include <sys/socket.h>
#include <sys/un.h>
#include <sys/poll.h>

#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>

static int lliowd_connfd = -1;
static int lliowd_watchfd = -2;

static void lliowd_getwatchfd() {

  // lliowd_connfd is alive. Either retrieve lliowd_watchfd from it,
  // or on failure or if the server doesn't present an fd, set lliowd_watchfd = -1.

  struct iovec iov[1];
  struct msghdr child_msg;

  char normalbuf;
  iov[0].iov_base = &normalbuf;
  iov[0].iov_len = 1;

  memset(&child_msg, 0, sizeof(child_msg));
  char cmsgbuf[CMSG_SPACE(sizeof(int))];
  child_msg.msg_control = cmsgbuf; // make place for the ancillary message to be received
  child_msg.msg_controllen = sizeof(cmsgbuf);
  child_msg.msg_iov = iov;
  child_msg.msg_iovlen = 1;

  int curflags = fcntl(lliowd_connfd, F_GETFL);
  curflags &= ~O_NONBLOCK;
  fcntl(lliowd_connfd, F_SETFL, curflags);

  int rc = recvmsg(lliowd_connfd, &child_msg, 0);
  if(rc <= 0) {

    // Server hung up or failed.
    close(lliowd_connfd);
    lliowd_watchfd = -1;
    return;

  }

  struct cmsghdr *cmsg = CMSG_FIRSTHDR(&child_msg);
  if ((!normalbuf) || cmsg == NULL || cmsg -> cmsg_type != SCM_RIGHTS) {

    // Server didn't send an FD (and/or sent a 0 in the normal message,
    // which indicates our files are already bad).
    close(lliowd_connfd);
    lliowd_watchfd = -1;
    return;

  }

  lliowd_watchfd = *((int*)CMSG_DATA(cmsg));
  close(lliowd_connfd);
  lliowd_connfd = -1;

}

#define UNIX_PATH_MAX 108

void lliowd_init() {

  lliowd_connfd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC | SOCK_NONBLOCK, 0);
  if(lliowd_connfd == -1) {

    // Mark failed
    lliowd_watchfd = -1;
    return;

  }

  struct sockaddr_un bindaddr;
  bindaddr.sun_family = AF_UNIX;
  
  const char* homedir = getenv("HOME");
  if(!homedir) {
    
    lliowd_watchfd = -1;
    close(lliowd_connfd);
    return;
    
  }

  if(snprintf(bindaddr.sun_path, UNIX_PATH_MAX, "%s/.lliowd-socket", homedir) >= UNIX_PATH_MAX) {

    lliowd_watchfd = -1;
    close(lliowd_connfd);
    return;

  }

  int ret = connect(lliowd_connfd, (struct sockaddr*)&bindaddr, sizeof(struct sockaddr_un));
  if(ret == 0) {

    lliowd_getwatchfd();

  }
  else if(errno != EINPROGRESS) {

    lliowd_watchfd = -1;
    close(lliowd_connfd);
    return;

  }

  // Else finish the process in lliowd_ok()
   
}

int lliowd_ok() {

  if(lliowd_watchfd == -1) {

    // Couldn't connect to the daemon, or did and it said
    // not to use specialised code, or an earlier check has already failed.
    return 0;

  }
  else if(lliowd_watchfd == -2) {

    // Connection not completed yet. Finish it:
    struct pollfd waitfd;
    waitfd.fd = lliowd_connfd;
    waitfd.events = POLLOUT;

    // Max wait: 5 seconds
    int pollret = poll(&waitfd, 1, 5000);

    if(pollret != 1) {

      // Give up.
      close(lliowd_connfd);
      lliowd_watchfd = -1;
      return 0;

    }

    // Connection completed! Check for error:
    int connect_error;
    socklen_t arglen = sizeof(int);
    int gso_ret = getsockopt(lliowd_connfd, SOL_SOCKET, SO_ERROR, &connect_error, &arglen);
    if(gso_ret == -1 || connect_error != 0) {

      close(lliowd_connfd);
      lliowd_watchfd = -1;
      return 0;

    }

    lliowd_getwatchfd();
    if(lliowd_watchfd == -1)
      return 0;

  }

  // Check if the inotify fd is readable. If it is, for now assume all our files are no longer good.
  // A better implementation should check individual files.

  {

    struct pollfd waitfd;
    waitfd.fd = lliowd_watchfd;
    waitfd.events = POLLIN;

    int pollret = poll(&waitfd, 1, 0);

    if(pollret != 0) {

      // Poll failed or inotify fd is readable. Either way, fail.
      close(lliowd_watchfd);
      lliowd_watchfd = -1;
      return 0;

    }

  }

  // All is well! Use specialised code:

  return 1;

}
