module.exports = {
    title: 'CPChian Docs',
    description: 'Just playing around',
    themeConfig: {
        nav: [
          { text: 'Guide', link: '/content/' },
          { text: 'API', link: '/content/api/rpc' },
          { text: 'Github', link: 'https://github.com/' },
        ],
        sidebar: [
          {
            title: 'QUICK START',
            collapsable: false,
            children: [
                '/content/quickstart/quickstart-beginner',
                '/content/quickstart/quickstart'
            ]
          },
          {
            title: 'PRELIMINARIES',
            collapsable: false,
            children: [
              '/content/preliminaries/abstract',
              '/content/preliminaries/basic_information',
              '/content/preliminaries/configuration',
              '/content/preliminaries/installation',
              '/content/preliminaries/overview'
            ]
          },
          {
            title: 'API',
            collapsable: false,
            children: [
              '/content/api/rpc',
              '/content/api/cpc_fusion'
            ]
          },
          {
            title: 'DETAILED ALGORITHMS',
            collapsable: false,
            children: [
              '/content/detailed_algorithms/consensus',
              '/content/detailed_algorithms/election',
              '/content/detailed_algorithms/implementation'
            ]
          },
          {
            title: 'SMART CONTRACTS',
            collapsable: false,
            children: [
              '/content/smart_contracts/built_in_sm',
              '/content/smart_contracts/reward_sm'
            ]
          },
          {
            title: 'TEST',
            collapsable: false,
            children: [
              '/content/test/test-overview',
              '/content/test/testcase'
            ]
          },
          {
            title: 'PERFORMANCE',
            collapsable: false,
            children: [
              '/content/performance/performance'
            ]
          },
          {
            title: 'MISC',
            collapsable: false,
            children: [
              '/content/misc/faq',
              '/content/misc/glossary',
              '/content/misc/mapping',
            ]
          },
        ],
        sidebarDepth: 2
      },
      markdown: {
        toc: {
          includeLevel:[1, 2, 3, 4]
        }
      },
      configureWebpack: {
        resolve: {
          alias: {
            // '@alias': 'path/to/some/dir'
          }
        }
      }
  }
