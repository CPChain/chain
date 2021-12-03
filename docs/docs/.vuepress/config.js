module.exports = {
    plugins:['@renovamen/vuepress-plugin-katex'],
    locales: {
      // 键名是该语言所属的子路径
      // 作为特例，默认语言可以使用 '/' 作为其路径。
      '/': {
        lang: 'en-US', // 将会被设置为 <html> 的 lang 属性
        title: 'CPChian Docs',
        description: 'Cpchain Docs -English'
      },
      '/zh/': {
        lang: 'zh-CN',
        title: 'CPChian 文档',
        description: 'Cpchain 文档 -中文'
      }
    },
    description: 'Just playing around',
    themeConfig: {
      locales:{
        '/': {
          selectText: 'Languages',
          label: 'English',
          ariaLabel: 'Languages',
          editLinkText: 'Edit this page on GitHub',
          serviceWorker: {
            updatePopup: {
              message: "New content is available.",
              buttonText: "Refresh"
            }
          },
          algolia: {},
          nav: [
            { text: 'Guide', link: '/content/index' },
            { text: 'API', link: '/content/api/rpc' },
            { text: 'solidity', link: '/solidity/docs/' },
            { text: 'Github', link: 'https://github.com/' },
          ],
          sidebar: {
              '/content/': [
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
                '/content/preliminaries/overview',
                '/content/preliminaries/installation',
                '/content/preliminaries/configuration'
              ]
            },
            {
              title: 'WALLETS',
              collapsable: false,
              children: [
                '/content/wallets/wallet_guide',
                '/content/wallets/mobile_app_wallets',
                '/content/wallets/web_wallets',
                {
                  title: 'HARDWARE WALLETS',
                  collapsable: true,
                  children: [
                    '/content/wallets/hardware_wallets/ledger'
                  ]
                },
                '/content/wallets/support'
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
                '/content/test/test-overview'
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
                '/content/misc/mapping'
              ]
            },
          ],
          '/solidity/': [
            {
              title: 'Solidity',
              collapsable: false,
              children: [
                '/solidity/docs/introduction-to-smart-contracts.md',
                '/solidity/docs/installing-solidity.md',
                '/solidity/docs/solidity-by-example.md',
                '/solidity/docs/solidity-in-depth.md',
                '/solidity/docs/security-considerations.md',
                '/solidity/docs/using-the-compiler.md',
                '/solidity/docs/metadata.md',
                '/solidity/docs/abi-spec.md',
                '/solidity/docs/julia.md',
                '/solidity/docs/style-guide.md',
                '/solidity/docs/common-patterns.md',
                '/solidity/docs/bugs.md',
                '/solidity/docs/contributing.md',
                '/solidity/docs/frequently-asked-questions.md',
              ]
            }
          ]
        },
          sidebarDepth: 2
        },
        '/zh/': {
          selectText: '选择语言',
          label: '简体中文',
          ariaLabel: 'Languages',
          editLinkText: 'Edit this page on GitHub',
          serviceWorker: {
            updatePopup: {
              message: "New content is available.",
              buttonText: "Refresh"
            }
          },
          algolia: {},
          nav: [
            { text: 'Guide', link: '/zh/content/' },
            { text: 'API', link: '/zh/content/api/rpc' },
            { text: 'solidity', link: '/zh/solidity/docs/' },
            { text: 'Github', link: 'https://github.com/' },
          ],
          sidebar: {
              '/zh/content/': [
            {
              title: '快速开始',
              collapsable: false,
              children: [
                  '/zh/content/quickstart/quickstart-beginner',
                  '/zh/content/quickstart/quickstart'
              ]
            },
            {
              title: 'PRELIMINARIES',
              collapsable: false,
              children: [
                '/zh/content/preliminaries/abstract',
                '/zh/content/preliminaries/basic_information',
                '/zh/content/preliminaries/configuration',
                '/zh/content/preliminaries/installation',
                '/zh/content/preliminaries/overview'
              ]
            },
            {
              title: '接口描述',
              collapsable: false,
              children: [
                '/zh/content/api/rpc',
                '/zh/content/api/cpc_fusion'
              ]
            },
            {
              title: '核心算法',
              collapsable: false,
              children: [
                '/zh/content/detailed_algorithms/consensus',
                '/zh/content/detailed_algorithms/election',
                '/zh/content/detailed_algorithms/implementation'
              ]
            },
            {
              title: '智能合约',
              collapsable: false,
              children: [
                '/zh/content/smart_contracts/built_in_sm',
                '/zh/content/smart_contracts/reward_sm'
              ]
            },
            {
              title: '测试',
              collapsable: false,
              children: [
                '/zh/content/test/test-overview'
              ]
            },
            {
              title: 'PERFORMANCE',
              collapsable: false,
              children: [
                '/zh/content/performance/performance'
              ]
            },
            {
              title: 'MISC',
              collapsable: false,
              children: [
                '/zh/content/misc/faq',
                '/zh/content/misc/glossary',
                '/zh/content/misc/mapping',
              ]
            },
          ],
          '/zh/solidity/': [
            {
              title: 'Solidity',
              collapsable: false,
              children: [
                '/zh/solidity/docs/introduction-to-smart-contracts.md',
                '/zh/solidity/docs/installing-solidity.md',
                '/zh/solidity/docs/solidity-by-example.md',
                '/zh/solidity/docs/solidity-in-depth.md',
                '/zh/solidity/docs/security-considerations.md',
                '/zh/solidity/docs/using-the-compiler.md',
                '/zh/solidity/docs/metadata.md',
                '/zh/solidity/docs/abi-spec.md',
                '/zh/solidity/docs/julia.md',
                '/zh/solidity/docs/style-guide.md',
                '/zh/solidity/docs/common-patterns.md',
                '/zh/solidity/docs/bugs.md',
                '/zh/solidity/docs/contributing.md',
                '/zh/solidity/docs/frequently-asked-questions.md',
              ]
            }
          ]
        },
          sidebarDepth: 2
        }
      }
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
