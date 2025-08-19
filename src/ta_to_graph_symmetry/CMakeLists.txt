# 添加共享库
add_library(ta_to_graph_symmetry SHARED ta_to_graph_symmetry.cpp)
#add_library(bliss STATIC "/home/xinyuliu/bliss-0.77/src/bliss.cc")
# include_directories("/home/xinyuliu/bliss-0.77/src")
# find_library(BLISS_LIB bliss HINTS "/home/xinyuliu/bliss-0.77/build/libbliss.so")
# link_directories("/home/xinyuliu/bliss-0.77/build/")
# 添加 include 路径
target_include_directories(ta_to_graph_symmetry PUBLIC
   # $<BUILD_INTERFACE:${NAUTY_DIR}>
    $<BUILD_INTERFACE:/home/xinyuliu/bliss-0.77/src>
    $<INSTALL_INTERFACE:include/ta_to_graph_symmetry>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}/tacos>
)
# set_target_properties(ta_to_graph_symmetry PROPERTIES
#     BUILD_RPATH "/home/xinyuliu/bliss-0.77/build"
# )
# 让当前子目录可以使用 Bliss 头文件
include_directories(${BLISS_INCLUDE_DIR})

# 让当前子目录链接 Bliss 库
target_link_libraries(ta_to_graph_symmetry PUBLIC ${BLISS_LIBRARY})


# 链接依赖库
target_link_libraries(ta_to_graph_symmetry PUBLIC automata mtl utilities spdlog::spdlog fmt::fmt)

# 安装共享库和头文件
install(TARGETS ta_to_graph_symmetry
    EXPORT TacosTargets
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
# 安装头文件
# install(DIRECTORY include/ta_to_graph_symmetry
#     DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/tacos
#     FILES_MATCHING
#     PATTERN "ta_to_graph_symmetry.hpp"
# )
install(DIRECTORY include/ta_to_graph_symmetry
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/tacos
    FILES_MATCHING
    PATTERN "*.hpp"
)
install(DIRECTORY include/ta_to_graph_symmetry
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/tacos
    FILES_MATCHING
    PATTERN "*.h"
)


target_compile_options(ta_to_graph_symmetry PRIVATE -Wno-error)

# 添加可执行文件
add_executable(na_use na_use.cpp)


# 链接 libbliss.a
#target_link_libraries(na_use )
target_link_libraries(na_use PRIVATE ta_to_graph_symmetry bliss)

install(DIRECTORY include/ta_to_graph_symmetry
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/tacos
)

