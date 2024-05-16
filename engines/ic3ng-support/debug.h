#pragma once
#define DEBUG_IC3

#ifdef DEBUG_IC3
#define D(...) logger.log(__VA_ARGS__)
#define LOGCAT (std::cout)

#else
#define  D(...) do{}while(0)

  struct nouse {
    template <class T>
    nouse & operator<<(const T &) {return *this;}
  };
  static nouse __nouse__;
#define LOGCAT (__nouse__)

#endif

