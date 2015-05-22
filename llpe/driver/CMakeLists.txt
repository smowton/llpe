
find_package(wxWidgets REQUIRED core base adv)

include(${wxWidgets_USE_FILE})

add_library(LLVMLLPEDriver MODULE Integrator.cpp)
target_link_libraries(LLVMLLPEDriver ${wxWidgets_LIBRARIES})
